/* ---------------------------------------------------------------------------- */
/*                  Atmel Microcontroller Software Support                      */
/*                       SAM Software Package License                           */
/* ---------------------------------------------------------------------------- */
/* Copyright (c) 2015, Atmel Corporation                                        */
/*                                                                              */
/* All rights reserved.                                                         */
/*                                                                              */
/* Redistribution and use in source and binary forms, with or without           */
/* modification, are permitted provided that the following condition is met:    */
/*                                                                              */
/* - Redistributions of source code must retain the above copyright notice,     */
/* this list of conditions and the disclaimer below.                            */
/*                                                                              */
/* Atmel's name may not be used to endorse or promote products derived from     */
/* this software without specific prior written permission.                     */
/*                                                                              */
/* DISCLAIMER:  THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR   */
/* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF */
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE   */
/* DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,      */
/* INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT */
/* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,  */
/* OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING         */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, */
/* EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                           */
/* ---------------------------------------------------------------------------- */

#ifndef _SAMA5D2_SMC_COMPONENT_
#define _SAMA5D2_SMC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Static Memory Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SMC Static Memory Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief SmcCs_number hardware registers */
typedef struct {
  __IO uint32_t HSMC_SETUP;   /**< \brief (SmcCs_number Offset: 0x0) HSMC Setup Register */
  __IO uint32_t HSMC_PULSE;   /**< \brief (SmcCs_number Offset: 0x4) HSMC Pulse Register */
  __IO uint32_t HSMC_CYCLE;   /**< \brief (SmcCs_number Offset: 0x8) HSMC Cycle Register */
  __IO uint32_t HSMC_TIMINGS; /**< \brief (SmcCs_number Offset: 0xC) HSMC Timings Register */
  __IO uint32_t HSMC_MODE;    /**< \brief (SmcCs_number Offset: 0x10) HSMC Mode Register */
} SmcCs_number;
/** \brief SmcPmecc hardware registers */
typedef struct {
  __I uint32_t HSMC_PMECC[14]; /**< \brief (SmcPmecc Offset: 0x0) PMECC Redundancy x Register */
  __I uint32_t Reserved1[2];
} SmcPmecc;
/** \brief SmcRem hardware registers */
typedef struct {
  __I uint32_t HSMC_REM0_;  /**< \brief (SmcRem Offset: 0x0) PMECC Remainder 0 Register */
  __I uint32_t HSMC_REM1_;  /**< \brief (SmcRem Offset: 0x4) PMECC Remainder 1 Register */
  __I uint32_t HSMC_REM2_;  /**< \brief (SmcRem Offset: 0x8) PMECC Remainder 2 Register */
  __I uint32_t HSMC_REM3_;  /**< \brief (SmcRem Offset: 0xC) PMECC Remainder 3 Register */
  __I uint32_t HSMC_REM4_;  /**< \brief (SmcRem Offset: 0x10) PMECC Remainder 4 Register */
  __I uint32_t HSMC_REM5_;  /**< \brief (SmcRem Offset: 0x14) PMECC Remainder 5 Register */
  __I uint32_t HSMC_REM6_;  /**< \brief (SmcRem Offset: 0x18) PMECC Remainder 6 Register */
  __I uint32_t HSMC_REM7_;  /**< \brief (SmcRem Offset: 0x1C) PMECC Remainder 7 Register */
  __I uint32_t HSMC_REM8_;  /**< \brief (SmcRem Offset: 0x20) PMECC Remainder 8 Register */
  __I uint32_t HSMC_REM9_;  /**< \brief (SmcRem Offset: 0x24) PMECC Remainder 9 Register */
  __I uint32_t HSMC_REM10_; /**< \brief (SmcRem Offset: 0x28) PMECC Remainder 10 Register */
  __I uint32_t HSMC_REM11_; /**< \brief (SmcRem Offset: 0x2C) PMECC Remainder 11 Register */
  __I uint32_t HSMC_REM12_; /**< \brief (SmcRem Offset: 0x30) PMECC Remainder 12 Register */
  __I uint32_t HSMC_REM13_; /**< \brief (SmcRem Offset: 0x34) PMECC Remainder 13 Register */
  __I uint32_t HSMC_REM14_; /**< \brief (SmcRem Offset: 0x38) PMECC Remainder 14 Register */
  __I uint32_t HSMC_REM15_; /**< \brief (SmcRem Offset: 0x3C) PMECC Remainder 15 Register */
} SmcRem;
/** \brief Smc hardware registers */
#define SMCPMECC_NUMBER 8
#define SMCREM_NUMBER 8
#define SMCCS_NUMBER_NUMBER 4
typedef struct {
  __IO uint32_t     HSMC_CFG;                           /**< \brief (Smc Offset: 0x000) HSMC NFC Configuration Register */
  __O  uint32_t     HSMC_CTRL;                          /**< \brief (Smc Offset: 0x004) HSMC NFC Control Register */
  __I  uint32_t     HSMC_SR;                            /**< \brief (Smc Offset: 0x008) HSMC NFC Status Register */
  __O  uint32_t     HSMC_IER;                           /**< \brief (Smc Offset: 0x00C) HSMC NFC Interrupt Enable Register */
  __O  uint32_t     HSMC_IDR;                           /**< \brief (Smc Offset: 0x010) HSMC NFC Interrupt Disable Register */
  __I  uint32_t     HSMC_IMR;                           /**< \brief (Smc Offset: 0x014) HSMC NFC Interrupt Mask Register */
  __IO uint32_t     HSMC_ADDR;                          /**< \brief (Smc Offset: 0x018) HSMC NFC Address Cycle Zero Register */
  __IO uint32_t     HSMC_BANK;                          /**< \brief (Smc Offset: 0x01C) HSMC Bank Address Register */
  __I  uint32_t     Reserved1[20];
  __IO uint32_t     HSMC_PMECCFG;                       /**< \brief (Smc Offset: 0x070) PMECC Configuration Register */
  __IO uint32_t     HSMC_PMECCSAREA;                    /**< \brief (Smc Offset: 0x074) PMECC Spare Area Size Register */
  __IO uint32_t     HSMC_PMECCSADDR;                    /**< \brief (Smc Offset: 0x078) PMECC Start Address Register */
  __IO uint32_t     HSMC_PMECCEADDR;                    /**< \brief (Smc Offset: 0x07C) PMECC End Address Register */
  __I  uint32_t     Reserved2[1];
  __O  uint32_t     HSMC_PMECCTRL;                      /**< \brief (Smc Offset: 0x084) PMECC Control Register */
  __I  uint32_t     HSMC_PMECCSR;                       /**< \brief (Smc Offset: 0x088) PMECC Status Register */
  __O  uint32_t     HSMC_PMECCIER;                      /**< \brief (Smc Offset: 0x08C) PMECC Interrupt Enable register */
  __O  uint32_t     HSMC_PMECCIDR;                      /**< \brief (Smc Offset: 0x090) PMECC Interrupt Disable Register */
  __I  uint32_t     HSMC_PMECCIMR;                      /**< \brief (Smc Offset: 0x094) PMECC Interrupt Mask Register */
  __I  uint32_t     HSMC_PMECCISR;                      /**< \brief (Smc Offset: 0x098) PMECC Interrupt Status Register */
  __I  uint32_t     Reserved3[5];
       SmcPmecc     SMC_PMECC[SMCPMECC_NUMBER];         /**< \brief (Smc Offset: 0xB0) sec_num = 0 .. 7 */
       SmcRem       SMC_REM[SMCREM_NUMBER];             /**< \brief (Smc Offset: 0x2B0) sec_num = 0 .. 7 */
  __I  uint32_t     Reserved4[20];
  __IO uint32_t     HSMC_ELCFG;                         /**< \brief (Smc Offset: 0x500) PMECC Error Location Configuration Register */
  __I  uint32_t     HSMC_ELPRIM;                        /**< \brief (Smc Offset: 0x504) PMECC Error Location Primitive Register */
  __O  uint32_t     HSMC_ELEN;                          /**< \brief (Smc Offset: 0x508) PMECC Error Location Enable Register */
  __O  uint32_t     HSMC_ELDIS;                         /**< \brief (Smc Offset: 0x50C) PMECC Error Location Disable Register */
  __I  uint32_t     HSMC_ELSR;                          /**< \brief (Smc Offset: 0x510) PMECC Error Location Status Register */
  __O  uint32_t     HSMC_ELIER;                         /**< \brief (Smc Offset: 0x514) PMECC Error Location Interrupt Enable register */
  __O  uint32_t     HSMC_ELIDR;                         /**< \brief (Smc Offset: 0x518) PMECC Error Location Interrupt Disable Register */
  __I  uint32_t     HSMC_ELIMR;                         /**< \brief (Smc Offset: 0x51C) PMECC Error Location Interrupt Mask Register */
  __I  uint32_t     HSMC_ELISR;                         /**< \brief (Smc Offset: 0x520) PMECC Error Location Interrupt Status Register */
  __I  uint32_t     Reserved5[1];
  __I  uint32_t     HSMC_SIGMA0;                        /**< \brief (Smc Offset: 0x528) PMECC Error Location SIGMA 0 Register */
  __IO uint32_t     HSMC_SIGMA1;                        /**< \brief (Smc Offset: 0x52C) PMECC Error Location SIGMA 1 Register */
  __IO uint32_t     HSMC_SIGMA2;                        /**< \brief (Smc Offset: 0x530) PMECC Error Location SIGMA 2 Register */
  __IO uint32_t     HSMC_SIGMA3;                        /**< \brief (Smc Offset: 0x534) PMECC Error Location SIGMA 3 Register */
  __IO uint32_t     HSMC_SIGMA4;                        /**< \brief (Smc Offset: 0x538) PMECC Error Location SIGMA 4 Register */
  __IO uint32_t     HSMC_SIGMA5;                        /**< \brief (Smc Offset: 0x53C) PMECC Error Location SIGMA 5 Register */
  __IO uint32_t     HSMC_SIGMA6;                        /**< \brief (Smc Offset: 0x540) PMECC Error Location SIGMA 6 Register */
  __IO uint32_t     HSMC_SIGMA7;                        /**< \brief (Smc Offset: 0x544) PMECC Error Location SIGMA 7 Register */
  __IO uint32_t     HSMC_SIGMA8;                        /**< \brief (Smc Offset: 0x548) PMECC Error Location SIGMA 8 Register */
  __IO uint32_t     HSMC_SIGMA9;                        /**< \brief (Smc Offset: 0x54C) PMECC Error Location SIGMA 9 Register */
  __IO uint32_t     HSMC_SIGMA10;                       /**< \brief (Smc Offset: 0x550) PMECC Error Location SIGMA 10 Register */
  __IO uint32_t     HSMC_SIGMA11;                       /**< \brief (Smc Offset: 0x554) PMECC Error Location SIGMA 11 Register */
  __IO uint32_t     HSMC_SIGMA12;                       /**< \brief (Smc Offset: 0x558) PMECC Error Location SIGMA 12 Register */
  __IO uint32_t     HSMC_SIGMA13;                       /**< \brief (Smc Offset: 0x55C) PMECC Error Location SIGMA 13 Register */
  __IO uint32_t     HSMC_SIGMA14;                       /**< \brief (Smc Offset: 0x560) PMECC Error Location SIGMA 14 Register */
  __IO uint32_t     HSMC_SIGMA15;                       /**< \brief (Smc Offset: 0x564) PMECC Error Location SIGMA 15 Register */
  __IO uint32_t     HSMC_SIGMA16;                       /**< \brief (Smc Offset: 0x568) PMECC Error Location SIGMA 16 Register */
  __IO uint32_t     HSMC_SIGMA17;                       /**< \brief (Smc Offset: 0x56C) PMECC Error Location SIGMA 17 Register */
  __IO uint32_t     HSMC_SIGMA18;                       /**< \brief (Smc Offset: 0x570) PMECC Error Location SIGMA 18 Register */
  __IO uint32_t     HSMC_SIGMA19;                       /**< \brief (Smc Offset: 0x574) PMECC Error Location SIGMA 19 Register */
  __IO uint32_t     HSMC_SIGMA20;                       /**< \brief (Smc Offset: 0x578) PMECC Error Location SIGMA 20 Register */
  __IO uint32_t     HSMC_SIGMA21;                       /**< \brief (Smc Offset: 0x57C) PMECC Error Location SIGMA 21 Register */
  __IO uint32_t     HSMC_SIGMA22;                       /**< \brief (Smc Offset: 0x580) PMECC Error Location SIGMA 22 Register */
  __IO uint32_t     HSMC_SIGMA23;                       /**< \brief (Smc Offset: 0x584) PMECC Error Location SIGMA 23 Register */
  __IO uint32_t     HSMC_SIGMA24;                       /**< \brief (Smc Offset: 0x588) PMECC Error Location SIGMA 24 Register */
  __IO uint32_t     HSMC_SIGMA25;                       /**< \brief (Smc Offset: 0x58C) PMECC Error Location SIGMA 25 Register */
  __IO uint32_t     HSMC_SIGMA26;                       /**< \brief (Smc Offset: 0x590) PMECC Error Location SIGMA 26 Register */
  __IO uint32_t     HSMC_SIGMA27;                       /**< \brief (Smc Offset: 0x594) PMECC Error Location SIGMA 27 Register */
  __IO uint32_t     HSMC_SIGMA28;                       /**< \brief (Smc Offset: 0x598) PMECC Error Location SIGMA 28 Register */
  __IO uint32_t     HSMC_SIGMA29;                       /**< \brief (Smc Offset: 0x59C) PMECC Error Location SIGMA 29 Register */
  __IO uint32_t     HSMC_SIGMA30;                       /**< \brief (Smc Offset: 0x5A0) PMECC Error Location SIGMA 30 Register */
  __IO uint32_t     HSMC_SIGMA31;                       /**< \brief (Smc Offset: 0x5A4) PMECC Error Location SIGMA 31 Register */
  __IO uint32_t     HSMC_SIGMA32;                       /**< \brief (Smc Offset: 0x5A8) PMECC Error Location SIGMA 32 Register */
  __I  uint32_t     HSMC_ERRLOC0;                       /**< \brief (Smc Offset: 0x5AC) PMECC Error Location 0 Register */
  __I  uint32_t     HSMC_ERRLOC1;                       /**< \brief (Smc Offset: 0x5B0) PMECC Error Location 1 Register */
  __I  uint32_t     HSMC_ERRLOC2;                       /**< \brief (Smc Offset: 0x5B4) PMECC Error Location 2 Register */
  __I  uint32_t     HSMC_ERRLOC3;                       /**< \brief (Smc Offset: 0x5B8) PMECC Error Location 3 Register */
  __I  uint32_t     HSMC_ERRLOC4;                       /**< \brief (Smc Offset: 0x5BC) PMECC Error Location 4 Register */
  __I  uint32_t     HSMC_ERRLOC5;                       /**< \brief (Smc Offset: 0x5C0) PMECC Error Location 5 Register */
  __I  uint32_t     HSMC_ERRLOC6;                       /**< \brief (Smc Offset: 0x5C4) PMECC Error Location 6 Register */
  __I  uint32_t     HSMC_ERRLOC7;                       /**< \brief (Smc Offset: 0x5C8) PMECC Error Location 7 Register */
  __I  uint32_t     HSMC_ERRLOC8;                       /**< \brief (Smc Offset: 0x5CC) PMECC Error Location 8 Register */
  __I  uint32_t     HSMC_ERRLOC9;                       /**< \brief (Smc Offset: 0x5D0) PMECC Error Location 9 Register */
  __I  uint32_t     HSMC_ERRLOC10;                      /**< \brief (Smc Offset: 0x5D4) PMECC Error Location 10 Register */
  __I  uint32_t     HSMC_ERRLOC11;                      /**< \brief (Smc Offset: 0x5D8) PMECC Error Location 11 Register */
  __I  uint32_t     HSMC_ERRLOC12;                      /**< \brief (Smc Offset: 0x5DC) PMECC Error Location 12 Register */
  __I  uint32_t     HSMC_ERRLOC13;                      /**< \brief (Smc Offset: 0x5E0) PMECC Error Location 13 Register */
  __I  uint32_t     HSMC_ERRLOC14;                      /**< \brief (Smc Offset: 0x5E4) PMECC Error Location 14 Register */
  __I  uint32_t     HSMC_ERRLOC15;                      /**< \brief (Smc Offset: 0x5E8) PMECC Error Location 15 Register */
  __I  uint32_t     HSMC_ERRLOC16;                      /**< \brief (Smc Offset: 0x5EC) PMECC Error Location 16 Register */
  __I  uint32_t     HSMC_ERRLOC17;                      /**< \brief (Smc Offset: 0x5F0) PMECC Error Location 17 Register */
  __I  uint32_t     HSMC_ERRLOC18;                      /**< \brief (Smc Offset: 0x5F4) PMECC Error Location 18 Register */
  __I  uint32_t     HSMC_ERRLOC19;                      /**< \brief (Smc Offset: 0x5F8) PMECC Error Location 19 Register */
  __I  uint32_t     HSMC_ERRLOC20;                      /**< \brief (Smc Offset: 0x5FC) PMECC Error Location 20 Register */
  __I  uint32_t     HSMC_ERRLOC21;                      /**< \brief (Smc Offset: 0x600) PMECC Error Location 21 Register */
  __I  uint32_t     HSMC_ERRLOC22;                      /**< \brief (Smc Offset: 0x604) PMECC Error Location 22 Register */
  __I  uint32_t     HSMC_ERRLOC23;                      /**< \brief (Smc Offset: 0x608) PMECC Error Location 23 Register */
  __I  uint32_t     HSMC_ERRLOC24;                      /**< \brief (Smc Offset: 0x60C) PMECC Error Location 24 Register */
  __I  uint32_t     HSMC_ERRLOC25;                      /**< \brief (Smc Offset: 0x610) PMECC Error Location 25 Register */
  __I  uint32_t     HSMC_ERRLOC26;                      /**< \brief (Smc Offset: 0x614) PMECC Error Location 26 Register */
  __I  uint32_t     HSMC_ERRLOC27;                      /**< \brief (Smc Offset: 0x618) PMECC Error Location 27 Register */
  __I  uint32_t     HSMC_ERRLOC28;                      /**< \brief (Smc Offset: 0x61C) PMECC Error Location 28 Register */
  __I  uint32_t     HSMC_ERRLOC29;                      /**< \brief (Smc Offset: 0x620) PMECC Error Location 29 Register */
  __I  uint32_t     HSMC_ERRLOC30;                      /**< \brief (Smc Offset: 0x624) PMECC Error Location 30 Register */
  __I  uint32_t     HSMC_ERRLOC31;                      /**< \brief (Smc Offset: 0x628) PMECC Error Location 31 Register */
  __I  uint32_t     Reserved6[53];
       SmcCs_number SMC_CS_NUMBER[SMCCS_NUMBER_NUMBER]; /**< \brief (Smc Offset: 0x700) CS_number = 0 .. 3 */
  __I  uint32_t     Reserved7[20];
  __IO uint32_t     HSMC_OCMS;                          /**< \brief (Smc Offset: 0x7A0) HSMC Off Chip Memory Scrambling Register */
  __O  uint32_t     HSMC_KEY1;                          /**< \brief (Smc Offset: 0x7A4) HSMC Off Chip Memory Scrambling KEY1 Register */
  __O  uint32_t     HSMC_KEY2;                          /**< \brief (Smc Offset: 0x7A8) HSMC Off Chip Memory Scrambling KEY2 Register */
  __I  uint32_t     Reserved8[14];
  __IO uint32_t     HSMC_WPMR;                          /**< \brief (Smc Offset: 0x7E4) HSMC Write Protection Mode Register */
  __I  uint32_t     HSMC_WPSR;                          /**< \brief (Smc Offset: 0x7E8) HSMC Write Protection Status Register */
  __I  uint32_t     Reserved9[4];
  __I  uint32_t     HSMC_VERSION;                       /**< \brief (Smc Offset: 0x7FC) HSMC Version Register */
} Smc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- HSMC_CFG : (SMC Offset: 0x000) HSMC NFC Configuration Register -------- */
#define HSMC_CFG_PAGESIZE_Pos 0
#define HSMC_CFG_PAGESIZE_Msk (0x7u << HSMC_CFG_PAGESIZE_Pos) /**< \brief (HSMC_CFG) Page Size of the NAND Flash Device */
#define HSMC_CFG_PAGESIZE(value) ((HSMC_CFG_PAGESIZE_Msk & ((value) << HSMC_CFG_PAGESIZE_Pos)))
#define   HSMC_CFG_PAGESIZE_PS512 (0x0u << 0) /**< \brief (HSMC_CFG) Main area 512 bytes */
#define   HSMC_CFG_PAGESIZE_PS1024 (0x1u << 0) /**< \brief (HSMC_CFG) Main area 1024 bytes */
#define   HSMC_CFG_PAGESIZE_PS2048 (0x2u << 0) /**< \brief (HSMC_CFG) Main area 2048 bytes */
#define   HSMC_CFG_PAGESIZE_PS4096 (0x3u << 0) /**< \brief (HSMC_CFG) Main area 4096 bytes */
#define   HSMC_CFG_PAGESIZE_PS8192 (0x4u << 0) /**< \brief (HSMC_CFG) Main area 8192 bytes */
#define HSMC_CFG_WSPARE (0x1u << 8) /**< \brief (HSMC_CFG) Write Spare Area */
#define HSMC_CFG_RSPARE (0x1u << 9) /**< \brief (HSMC_CFG) Read Spare Area */
#define HSMC_CFG_EDGECTRL (0x1u << 12) /**< \brief (HSMC_CFG) Rising/Falling Edge Detection Control */
#define HSMC_CFG_RBEDGE (0x1u << 13) /**< \brief (HSMC_CFG) Ready/Busy Signal Edge Detection */
#define HSMC_CFG_DTOCYC_Pos 16
#define HSMC_CFG_DTOCYC_Msk (0xfu << HSMC_CFG_DTOCYC_Pos) /**< \brief (HSMC_CFG) Data Timeout Cycle Number */
#define HSMC_CFG_DTOCYC(value) ((HSMC_CFG_DTOCYC_Msk & ((value) << HSMC_CFG_DTOCYC_Pos)))
#define HSMC_CFG_DTOMUL_Pos 20
#define HSMC_CFG_DTOMUL_Msk (0x7u << HSMC_CFG_DTOMUL_Pos) /**< \brief (HSMC_CFG) Data Timeout Multiplier */
#define HSMC_CFG_DTOMUL(value) ((HSMC_CFG_DTOMUL_Msk & ((value) << HSMC_CFG_DTOMUL_Pos)))
#define   HSMC_CFG_DTOMUL_X1 (0x0u << 20) /**< \brief (HSMC_CFG) DTOCYC */
#define   HSMC_CFG_DTOMUL_X16 (0x1u << 20) /**< \brief (HSMC_CFG) DTOCYC x 16 */
#define   HSMC_CFG_DTOMUL_X128 (0x2u << 20) /**< \brief (HSMC_CFG) DTOCYC x 128 */
#define   HSMC_CFG_DTOMUL_X256 (0x3u << 20) /**< \brief (HSMC_CFG) DTOCYC x 256 */
#define   HSMC_CFG_DTOMUL_X1024 (0x4u << 20) /**< \brief (HSMC_CFG) DTOCYC x 1024 */
#define   HSMC_CFG_DTOMUL_X4096 (0x5u << 20) /**< \brief (HSMC_CFG) DTOCYC x 4096 */
#define   HSMC_CFG_DTOMUL_X65536 (0x6u << 20) /**< \brief (HSMC_CFG) DTOCYC x 65536 */
#define   HSMC_CFG_DTOMUL_X1048576 (0x7u << 20) /**< \brief (HSMC_CFG) DTOCYC x 1048576 */
#define HSMC_CFG_NFCSPARESIZE_Pos 24
#define HSMC_CFG_NFCSPARESIZE_Msk (0x7fu << HSMC_CFG_NFCSPARESIZE_Pos) /**< \brief (HSMC_CFG) NAND Flash Spare Area Size Retrieved by the Host Controller */
#define HSMC_CFG_NFCSPARESIZE(value) ((HSMC_CFG_NFCSPARESIZE_Msk & ((value) << HSMC_CFG_NFCSPARESIZE_Pos)))
/* -------- HSMC_CTRL : (SMC Offset: 0x004) HSMC NFC Control Register -------- */
#define HSMC_CTRL_NFCEN (0x1u << 0) /**< \brief (HSMC_CTRL) NAND Flash Controller Enable */
#define HSMC_CTRL_NFCDIS (0x1u << 1) /**< \brief (HSMC_CTRL) NAND Flash Controller Disable */
/* -------- HSMC_SR : (SMC Offset: 0x008) HSMC NFC Status Register -------- */
#define HSMC_SR_SMCSTS (0x1u << 0) /**< \brief (HSMC_SR) NAND Flash Controller Status (this field cannot be reset) */
#define HSMC_SR_RB_RISE (0x1u << 4) /**< \brief (HSMC_SR) Selected Ready Busy Rising Edge Detected */
#define HSMC_SR_RB_FALL (0x1u << 5) /**< \brief (HSMC_SR) Selected Ready Busy Falling Edge Detected */
#define HSMC_SR_NFCBUSY (0x1u << 8) /**< \brief (HSMC_SR) NFC Busy (this field cannot be reset) */
#define HSMC_SR_NFCWR (0x1u << 11) /**< \brief (HSMC_SR) NFC Write/Read Operation (this field cannot be reset) */
#define HSMC_SR_NFCSID_Pos 12
#define HSMC_SR_NFCSID_Msk (0x7u << HSMC_SR_NFCSID_Pos) /**< \brief (HSMC_SR) NFC Chip Select ID (this field cannot be reset) */
#define HSMC_SR_XFRDONE (0x1u << 16) /**< \brief (HSMC_SR) NFC Data Transfer Terminated */
#define HSMC_SR_CMDDONE (0x1u << 17) /**< \brief (HSMC_SR) Command Done */
#define HSMC_SR_DTOE (0x1u << 20) /**< \brief (HSMC_SR) Data Timeout Error */
#define HSMC_SR_UNDEF (0x1u << 21) /**< \brief (HSMC_SR) Undefined Area Error */
#define HSMC_SR_AWB (0x1u << 22) /**< \brief (HSMC_SR) Accessing While Busy */
#define HSMC_SR_NFCASE (0x1u << 23) /**< \brief (HSMC_SR) NFC Access Size Error */
#define HSMC_SR_RB_EDGE3 (0x1u << 27) /**< \brief (HSMC_SR) Ready/Busy Line 3 Edge Detected */
/* -------- HSMC_IER : (SMC Offset: 0x00C) HSMC NFC Interrupt Enable Register -------- */
#define HSMC_IER_RB_RISE (0x1u << 4) /**< \brief (HSMC_IER) Ready Busy Rising Edge Detection Interrupt Enable */
#define HSMC_IER_RB_FALL (0x1u << 5) /**< \brief (HSMC_IER) Ready Busy Falling Edge Detection Interrupt Enable */
#define HSMC_IER_XFRDONE (0x1u << 16) /**< \brief (HSMC_IER) Transfer Done Interrupt Enable */
#define HSMC_IER_CMDDONE (0x1u << 17) /**< \brief (HSMC_IER) Command Done Interrupt Enable */
#define HSMC_IER_DTOE (0x1u << 20) /**< \brief (HSMC_IER) Data Timeout Error Interrupt Enable */
#define HSMC_IER_UNDEF (0x1u << 21) /**< \brief (HSMC_IER) Undefined Area Access Interrupt Enable */
#define HSMC_IER_AWB (0x1u << 22) /**< \brief (HSMC_IER) Accessing While Busy Interrupt Enable */
#define HSMC_IER_NFCASE (0x1u << 23) /**< \brief (HSMC_IER) NFC Access Size Error Interrupt Enable */
#define HSMC_IER_RB_EDGE3 (0x1u << 27) /**< \brief (HSMC_IER) Ready/Busy Line 3 Interrupt Enable */
/* -------- HSMC_IDR : (SMC Offset: 0x010) HSMC NFC Interrupt Disable Register -------- */
#define HSMC_IDR_RB_RISE (0x1u << 4) /**< \brief (HSMC_IDR) Ready Busy Rising Edge Detection Interrupt Disable */
#define HSMC_IDR_RB_FALL (0x1u << 5) /**< \brief (HSMC_IDR) Ready Busy Falling Edge Detection Interrupt Disable */
#define HSMC_IDR_XFRDONE (0x1u << 16) /**< \brief (HSMC_IDR) Transfer Done Interrupt Disable */
#define HSMC_IDR_CMDDONE (0x1u << 17) /**< \brief (HSMC_IDR) Command Done Interrupt Disable */
#define HSMC_IDR_DTOE (0x1u << 20) /**< \brief (HSMC_IDR) Data Timeout Error Interrupt Disable */
#define HSMC_IDR_UNDEF (0x1u << 21) /**< \brief (HSMC_IDR) Undefined Area Access Interrupt Disable */
#define HSMC_IDR_AWB (0x1u << 22) /**< \brief (HSMC_IDR) Accessing While Busy Interrupt Disable */
#define HSMC_IDR_NFCASE (0x1u << 23) /**< \brief (HSMC_IDR) NFC Access Size Error Interrupt Disable */
#define HSMC_IDR_RB_EDGE3 (0x1u << 27) /**< \brief (HSMC_IDR) Ready/Busy Line 3 Interrupt Disable */
/* -------- HSMC_IMR : (SMC Offset: 0x014) HSMC NFC Interrupt Mask Register -------- */
#define HSMC_IMR_RB_RISE (0x1u << 4) /**< \brief (HSMC_IMR) Ready Busy Rising Edge Detection Interrupt Mask */
#define HSMC_IMR_RB_FALL (0x1u << 5) /**< \brief (HSMC_IMR) Ready Busy Falling Edge Detection Interrupt Mask */
#define HSMC_IMR_XFRDONE (0x1u << 16) /**< \brief (HSMC_IMR) Transfer Done Interrupt Mask */
#define HSMC_IMR_CMDDONE (0x1u << 17) /**< \brief (HSMC_IMR) Command Done Interrupt Mask */
#define HSMC_IMR_DTOE (0x1u << 20) /**< \brief (HSMC_IMR) Data Timeout Error Interrupt Mask */
#define HSMC_IMR_UNDEF (0x1u << 21) /**< \brief (HSMC_IMR) Undefined Area Access Interrupt Mask5 */
#define HSMC_IMR_AWB (0x1u << 22) /**< \brief (HSMC_IMR) Accessing While Busy Interrupt Mask */
#define HSMC_IMR_NFCASE (0x1u << 23) /**< \brief (HSMC_IMR) NFC Access Size Error Interrupt Mask */
#define HSMC_IMR_RB_EDGE3 (0x1u << 27) /**< \brief (HSMC_IMR) Ready/Busy Line 3 Interrupt Mask */
/* -------- HSMC_ADDR : (SMC Offset: 0x018) HSMC NFC Address Cycle Zero Register -------- */
#define HSMC_ADDR_ADDR_CYCLE0_Pos 0
#define HSMC_ADDR_ADDR_CYCLE0_Msk (0xffu << HSMC_ADDR_ADDR_CYCLE0_Pos) /**< \brief (HSMC_ADDR) NAND Flash Array Address Cycle 0 */
#define HSMC_ADDR_ADDR_CYCLE0(value) ((HSMC_ADDR_ADDR_CYCLE0_Msk & ((value) << HSMC_ADDR_ADDR_CYCLE0_Pos)))
/* -------- HSMC_BANK : (SMC Offset: 0x01C) HSMC Bank Address Register -------- */
#define HSMC_BANK_BANK (0x1u << 0) /**< \brief (HSMC_BANK) Bank Identifier */
/* -------- HSMC_PMECCFG : (SMC Offset: 0x070) PMECC Configuration Register -------- */
#define HSMC_PMECCFG_BCH_ERR_Pos 0
#define HSMC_PMECCFG_BCH_ERR_Msk (0x7u << HSMC_PMECCFG_BCH_ERR_Pos) /**< \brief (HSMC_PMECCFG) Error Correcting Capability */
#define HSMC_PMECCFG_BCH_ERR(value) ((HSMC_PMECCFG_BCH_ERR_Msk & ((value) << HSMC_PMECCFG_BCH_ERR_Pos)))
#define   HSMC_PMECCFG_BCH_ERR_BCH_ERR2 (0x0u << 0) /**< \brief (HSMC_PMECCFG) 2 errors */
#define   HSMC_PMECCFG_BCH_ERR_BCH_ERR4 (0x1u << 0) /**< \brief (HSMC_PMECCFG) 4 errors */
#define   HSMC_PMECCFG_BCH_ERR_BCH_ERR8 (0x2u << 0) /**< \brief (HSMC_PMECCFG) 8 errors */
#define   HSMC_PMECCFG_BCH_ERR_BCH_ERR12 (0x3u << 0) /**< \brief (HSMC_PMECCFG) 12 errors */
#define   HSMC_PMECCFG_BCH_ERR_BCH_ERR24 (0x4u << 0) /**< \brief (HSMC_PMECCFG) 24 errors */
#define   HSMC_PMECCFG_BCH_ERR_BCH_ERR32 (0x5u << 0) /**< \brief (HSMC_PMECCFG) 32 errors */
#define HSMC_PMECCFG_SECTORSZ (0x1u << 4) /**< \brief (HSMC_PMECCFG) Sector Size */
#define HSMC_PMECCFG_PAGESIZE_Pos 8
#define HSMC_PMECCFG_PAGESIZE_Msk (0x3u << HSMC_PMECCFG_PAGESIZE_Pos) /**< \brief (HSMC_PMECCFG) Number of Sectors in the Page */
#define HSMC_PMECCFG_PAGESIZE(value) ((HSMC_PMECCFG_PAGESIZE_Msk & ((value) << HSMC_PMECCFG_PAGESIZE_Pos)))
#define   HSMC_PMECCFG_PAGESIZE_PAGESIZE_1SEC (0x0u << 8) /**< \brief (HSMC_PMECCFG) 1 sector for main area (512 or 1024 bytes) */
#define   HSMC_PMECCFG_PAGESIZE_PAGESIZE_2SEC (0x1u << 8) /**< \brief (HSMC_PMECCFG) 2 sectors for main area (1024 or 2048 bytes) */
#define   HSMC_PMECCFG_PAGESIZE_PAGESIZE_4SEC (0x2u << 8) /**< \brief (HSMC_PMECCFG) 4 sectors for main area (2048 or 4096 bytes) */
#define   HSMC_PMECCFG_PAGESIZE_PAGESIZE_8SEC (0x3u << 8) /**< \brief (HSMC_PMECCFG) 8 sectors for main area (4096 or 8192 bytes) */
#define HSMC_PMECCFG_NANDWR (0x1u << 12) /**< \brief (HSMC_PMECCFG) NAND Write Access */
#define HSMC_PMECCFG_SPAREEN (0x1u << 16) /**< \brief (HSMC_PMECCFG) Spare Enable */
#define HSMC_PMECCFG_AUTO (0x1u << 20) /**< \brief (HSMC_PMECCFG) Automatic Mode Enable */
/* -------- HSMC_PMECCSAREA : (SMC Offset: 0x074) PMECC Spare Area Size Register -------- */
#define HSMC_PMECCSAREA_SPARESIZE_Pos 0
#define HSMC_PMECCSAREA_SPARESIZE_Msk (0x1ffu << HSMC_PMECCSAREA_SPARESIZE_Pos) /**< \brief (HSMC_PMECCSAREA) Spare Area Size */
#define HSMC_PMECCSAREA_SPARESIZE(value) ((HSMC_PMECCSAREA_SPARESIZE_Msk & ((value) << HSMC_PMECCSAREA_SPARESIZE_Pos)))
/* -------- HSMC_PMECCSADDR : (SMC Offset: 0x078) PMECC Start Address Register -------- */
#define HSMC_PMECCSADDR_STARTADDR_Pos 0
#define HSMC_PMECCSADDR_STARTADDR_Msk (0x1ffu << HSMC_PMECCSADDR_STARTADDR_Pos) /**< \brief (HSMC_PMECCSADDR) ECC Area Start Address */
#define HSMC_PMECCSADDR_STARTADDR(value) ((HSMC_PMECCSADDR_STARTADDR_Msk & ((value) << HSMC_PMECCSADDR_STARTADDR_Pos)))
/* -------- HSMC_PMECCEADDR : (SMC Offset: 0x07C) PMECC End Address Register -------- */
#define HSMC_PMECCEADDR_ENDADDR_Pos 0
#define HSMC_PMECCEADDR_ENDADDR_Msk (0x1ffu << HSMC_PMECCEADDR_ENDADDR_Pos) /**< \brief (HSMC_PMECCEADDR) ECC Area End Address */
#define HSMC_PMECCEADDR_ENDADDR(value) ((HSMC_PMECCEADDR_ENDADDR_Msk & ((value) << HSMC_PMECCEADDR_ENDADDR_Pos)))
/* -------- HSMC_PMECCTRL : (SMC Offset: 0x084) PMECC Control Register -------- */
#define HSMC_PMECCTRL_RST (0x1u << 0) /**< \brief (HSMC_PMECCTRL) Reset the PMECC Module */
#define HSMC_PMECCTRL_DATA (0x1u << 1) /**< \brief (HSMC_PMECCTRL) Start a Data Phase */
#define HSMC_PMECCTRL_USER (0x1u << 2) /**< \brief (HSMC_PMECCTRL) Start a User Mode Phase */
#define HSMC_PMECCTRL_ENABLE (0x1u << 4) /**< \brief (HSMC_PMECCTRL) PMECC Enable */
#define HSMC_PMECCTRL_DISABLE (0x1u << 5) /**< \brief (HSMC_PMECCTRL) PMECC Enable */
/* -------- HSMC_PMECCSR : (SMC Offset: 0x088) PMECC Status Register -------- */
#define HSMC_PMECCSR_BUSY (0x1u << 0) /**< \brief (HSMC_PMECCSR) The kernel of the PMECC is busy */
#define HSMC_PMECCSR_ENABLE (0x1u << 4) /**< \brief (HSMC_PMECCSR) PMECC Enable bit */
/* -------- HSMC_PMECCIER : (SMC Offset: 0x08C) PMECC Interrupt Enable register -------- */
#define HSMC_PMECCIER_ERRIE (0x1u << 0) /**< \brief (HSMC_PMECCIER) Error Interrupt Enable */
/* -------- HSMC_PMECCIDR : (SMC Offset: 0x090) PMECC Interrupt Disable Register -------- */
#define HSMC_PMECCIDR_ERRID (0x1u << 0) /**< \brief (HSMC_PMECCIDR) Error Interrupt Disable */
/* -------- HSMC_PMECCIMR : (SMC Offset: 0x094) PMECC Interrupt Mask Register -------- */
#define HSMC_PMECCIMR_ERRIM (0x1u << 0) /**< \brief (HSMC_PMECCIMR) Error Interrupt Mask */
/* -------- HSMC_PMECCISR : (SMC Offset: 0x098) PMECC Interrupt Status Register -------- */
#define HSMC_PMECCISR_ERRIS_Pos 0
#define HSMC_PMECCISR_ERRIS_Msk (0xffu << HSMC_PMECCISR_ERRIS_Pos) /**< \brief (HSMC_PMECCISR) Error Interrupt Status Register */
/* -------- HSMC_PMECC[14] : (SMC Offset: N/A) PMECC Redundancy x Register -------- */
#define HSMC_PMECC_ECC_Pos 0
#define HSMC_PMECC_ECC_Msk (0xffffffffu << HSMC_PMECC_ECC_Pos) /**< \brief (HSMC_PMECC[14]) BCH Redundancy */
/* -------- HSMC_REM0_ : (SMC Offset: N/A) PMECC Remainder 0 Register -------- */
#define HSMC_REM0__REM2NP1_Pos 0
#define HSMC_REM0__REM2NP1_Msk (0x3fffu << HSMC_REM0__REM2NP1_Pos) /**< \brief (HSMC_REM0_) BCH Remainder 2 * N + 1 */
#define HSMC_REM0__REM2NP3_Pos 16
#define HSMC_REM0__REM2NP3_Msk (0x3fffu << HSMC_REM0__REM2NP3_Pos) /**< \brief (HSMC_REM0_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM1_ : (SMC Offset: N/A) PMECC Remainder 1 Register -------- */
#define HSMC_REM1__REM2NP1_Pos 0
#define HSMC_REM1__REM2NP1_Msk (0x3fffu << HSMC_REM1__REM2NP1_Pos) /**< \brief (HSMC_REM1_) BCH Remainder 2 * N + 1 */
#define HSMC_REM1__REM2NP3_Pos 16
#define HSMC_REM1__REM2NP3_Msk (0x3fffu << HSMC_REM1__REM2NP3_Pos) /**< \brief (HSMC_REM1_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM2_ : (SMC Offset: N/A) PMECC Remainder 2 Register -------- */
#define HSMC_REM2__REM2NP1_Pos 0
#define HSMC_REM2__REM2NP1_Msk (0x3fffu << HSMC_REM2__REM2NP1_Pos) /**< \brief (HSMC_REM2_) BCH Remainder 2 * N + 1 */
#define HSMC_REM2__REM2NP3_Pos 16
#define HSMC_REM2__REM2NP3_Msk (0x3fffu << HSMC_REM2__REM2NP3_Pos) /**< \brief (HSMC_REM2_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM3_ : (SMC Offset: N/A) PMECC Remainder 3 Register -------- */
#define HSMC_REM3__REM2NP1_Pos 0
#define HSMC_REM3__REM2NP1_Msk (0x3fffu << HSMC_REM3__REM2NP1_Pos) /**< \brief (HSMC_REM3_) BCH Remainder 2 * N + 1 */
#define HSMC_REM3__REM2NP3_Pos 16
#define HSMC_REM3__REM2NP3_Msk (0x3fffu << HSMC_REM3__REM2NP3_Pos) /**< \brief (HSMC_REM3_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM4_ : (SMC Offset: N/A) PMECC Remainder 4 Register -------- */
#define HSMC_REM4__REM2NP1_Pos 0
#define HSMC_REM4__REM2NP1_Msk (0x3fffu << HSMC_REM4__REM2NP1_Pos) /**< \brief (HSMC_REM4_) BCH Remainder 2 * N + 1 */
#define HSMC_REM4__REM2NP3_Pos 16
#define HSMC_REM4__REM2NP3_Msk (0x3fffu << HSMC_REM4__REM2NP3_Pos) /**< \brief (HSMC_REM4_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM5_ : (SMC Offset: N/A) PMECC Remainder 5 Register -------- */
#define HSMC_REM5__REM2NP1_Pos 0
#define HSMC_REM5__REM2NP1_Msk (0x3fffu << HSMC_REM5__REM2NP1_Pos) /**< \brief (HSMC_REM5_) BCH Remainder 2 * N + 1 */
#define HSMC_REM5__REM2NP3_Pos 16
#define HSMC_REM5__REM2NP3_Msk (0x3fffu << HSMC_REM5__REM2NP3_Pos) /**< \brief (HSMC_REM5_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM6_ : (SMC Offset: N/A) PMECC Remainder 6 Register -------- */
#define HSMC_REM6__REM2NP1_Pos 0
#define HSMC_REM6__REM2NP1_Msk (0x3fffu << HSMC_REM6__REM2NP1_Pos) /**< \brief (HSMC_REM6_) BCH Remainder 2 * N + 1 */
#define HSMC_REM6__REM2NP3_Pos 16
#define HSMC_REM6__REM2NP3_Msk (0x3fffu << HSMC_REM6__REM2NP3_Pos) /**< \brief (HSMC_REM6_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM7_ : (SMC Offset: N/A) PMECC Remainder 7 Register -------- */
#define HSMC_REM7__REM2NP1_Pos 0
#define HSMC_REM7__REM2NP1_Msk (0x3fffu << HSMC_REM7__REM2NP1_Pos) /**< \brief (HSMC_REM7_) BCH Remainder 2 * N + 1 */
#define HSMC_REM7__REM2NP3_Pos 16
#define HSMC_REM7__REM2NP3_Msk (0x3fffu << HSMC_REM7__REM2NP3_Pos) /**< \brief (HSMC_REM7_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM8_ : (SMC Offset: N/A) PMECC Remainder 8 Register -------- */
#define HSMC_REM8__REM2NP1_Pos 0
#define HSMC_REM8__REM2NP1_Msk (0x3fffu << HSMC_REM8__REM2NP1_Pos) /**< \brief (HSMC_REM8_) BCH Remainder 2 * N + 1 */
#define HSMC_REM8__REM2NP3_Pos 16
#define HSMC_REM8__REM2NP3_Msk (0x3fffu << HSMC_REM8__REM2NP3_Pos) /**< \brief (HSMC_REM8_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM9_ : (SMC Offset: N/A) PMECC Remainder 9 Register -------- */
#define HSMC_REM9__REM2NP1_Pos 0
#define HSMC_REM9__REM2NP1_Msk (0x3fffu << HSMC_REM9__REM2NP1_Pos) /**< \brief (HSMC_REM9_) BCH Remainder 2 * N + 1 */
#define HSMC_REM9__REM2NP3_Pos 16
#define HSMC_REM9__REM2NP3_Msk (0x3fffu << HSMC_REM9__REM2NP3_Pos) /**< \brief (HSMC_REM9_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM10_ : (SMC Offset: N/A) PMECC Remainder 10 Register -------- */
#define HSMC_REM10__REM2NP1_Pos 0
#define HSMC_REM10__REM2NP1_Msk (0x3fffu << HSMC_REM10__REM2NP1_Pos) /**< \brief (HSMC_REM10_) BCH Remainder 2 * N + 1 */
#define HSMC_REM10__REM2NP3_Pos 16
#define HSMC_REM10__REM2NP3_Msk (0x3fffu << HSMC_REM10__REM2NP3_Pos) /**< \brief (HSMC_REM10_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM11_ : (SMC Offset: N/A) PMECC Remainder 11 Register -------- */
#define HSMC_REM11__REM2NP1_Pos 0
#define HSMC_REM11__REM2NP1_Msk (0x3fffu << HSMC_REM11__REM2NP1_Pos) /**< \brief (HSMC_REM11_) BCH Remainder 2 * N + 1 */
#define HSMC_REM11__REM2NP3_Pos 16
#define HSMC_REM11__REM2NP3_Msk (0x3fffu << HSMC_REM11__REM2NP3_Pos) /**< \brief (HSMC_REM11_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM12_ : (SMC Offset: N/A) PMECC Remainder 12 Register -------- */
#define HSMC_REM12__REM2NP1_Pos 0
#define HSMC_REM12__REM2NP1_Msk (0x3fffu << HSMC_REM12__REM2NP1_Pos) /**< \brief (HSMC_REM12_) BCH Remainder 2 * N + 1 */
#define HSMC_REM12__REM2NP3_Pos 16
#define HSMC_REM12__REM2NP3_Msk (0x3fffu << HSMC_REM12__REM2NP3_Pos) /**< \brief (HSMC_REM12_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM13_ : (SMC Offset: N/A) PMECC Remainder 13 Register -------- */
#define HSMC_REM13__REM2NP1_Pos 0
#define HSMC_REM13__REM2NP1_Msk (0x3fffu << HSMC_REM13__REM2NP1_Pos) /**< \brief (HSMC_REM13_) BCH Remainder 2 * N + 1 */
#define HSMC_REM13__REM2NP3_Pos 16
#define HSMC_REM13__REM2NP3_Msk (0x3fffu << HSMC_REM13__REM2NP3_Pos) /**< \brief (HSMC_REM13_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM14_ : (SMC Offset: N/A) PMECC Remainder 14 Register -------- */
#define HSMC_REM14__REM2NP1_Pos 0
#define HSMC_REM14__REM2NP1_Msk (0x3fffu << HSMC_REM14__REM2NP1_Pos) /**< \brief (HSMC_REM14_) BCH Remainder 2 * N + 1 */
#define HSMC_REM14__REM2NP3_Pos 16
#define HSMC_REM14__REM2NP3_Msk (0x3fffu << HSMC_REM14__REM2NP3_Pos) /**< \brief (HSMC_REM14_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_REM15_ : (SMC Offset: N/A) PMECC Remainder 15 Register -------- */
#define HSMC_REM15__REM2NP1_Pos 0
#define HSMC_REM15__REM2NP1_Msk (0x3fffu << HSMC_REM15__REM2NP1_Pos) /**< \brief (HSMC_REM15_) BCH Remainder 2 * N + 1 */
#define HSMC_REM15__REM2NP3_Pos 16
#define HSMC_REM15__REM2NP3_Msk (0x3fffu << HSMC_REM15__REM2NP3_Pos) /**< \brief (HSMC_REM15_) BCH Remainder 2 * N + 3 */
/* -------- HSMC_ELCFG : (SMC Offset: 0x500) PMECC Error Location Configuration Register -------- */
#define HSMC_ELCFG_SECTORSZ (0x1u << 0) /**< \brief (HSMC_ELCFG) Sector Size */
#define HSMC_ELCFG_ERRNUM_Pos 16
#define HSMC_ELCFG_ERRNUM_Msk (0x1fu << HSMC_ELCFG_ERRNUM_Pos) /**< \brief (HSMC_ELCFG) Number of Errors */
#define HSMC_ELCFG_ERRNUM(value) ((HSMC_ELCFG_ERRNUM_Msk & ((value) << HSMC_ELCFG_ERRNUM_Pos)))
/* -------- HSMC_ELPRIM : (SMC Offset: 0x504) PMECC Error Location Primitive Register -------- */
#define HSMC_ELPRIM_PRIMITIV_Pos 0
#define HSMC_ELPRIM_PRIMITIV_Msk (0xffffu << HSMC_ELPRIM_PRIMITIV_Pos) /**< \brief (HSMC_ELPRIM) Primitive Polynomial */
/* -------- HSMC_ELEN : (SMC Offset: 0x508) PMECC Error Location Enable Register -------- */
#define HSMC_ELEN_ENINIT_Pos 0
#define HSMC_ELEN_ENINIT_Msk (0x3fffu << HSMC_ELEN_ENINIT_Pos) /**< \brief (HSMC_ELEN) Error Location Enable */
#define HSMC_ELEN_ENINIT(value) ((HSMC_ELEN_ENINIT_Msk & ((value) << HSMC_ELEN_ENINIT_Pos)))
/* -------- HSMC_ELDIS : (SMC Offset: 0x50C) PMECC Error Location Disable Register -------- */
#define HSMC_ELDIS_DIS (0x1u << 0) /**< \brief (HSMC_ELDIS) Disable Error Location Engine */
/* -------- HSMC_ELSR : (SMC Offset: 0x510) PMECC Error Location Status Register -------- */
#define HSMC_ELSR_BUSY (0x1u << 0) /**< \brief (HSMC_ELSR) Error Location Engine Busy */
/* -------- HSMC_ELIER : (SMC Offset: 0x514) PMECC Error Location Interrupt Enable register -------- */
#define HSMC_ELIER_DONE (0x1u << 0) /**< \brief (HSMC_ELIER) Computation Terminated Interrupt Enable */
/* -------- HSMC_ELIDR : (SMC Offset: 0x518) PMECC Error Location Interrupt Disable Register -------- */
#define HSMC_ELIDR_DONE (0x1u << 0) /**< \brief (HSMC_ELIDR) Computation Terminated Interrupt Disable */
/* -------- HSMC_ELIMR : (SMC Offset: 0x51C) PMECC Error Location Interrupt Mask Register -------- */
#define HSMC_ELIMR_DONE (0x1u << 0) /**< \brief (HSMC_ELIMR) Computation Terminated Interrupt Mask */
/* -------- HSMC_ELISR : (SMC Offset: 0x520) PMECC Error Location Interrupt Status Register -------- */
#define HSMC_ELISR_DONE (0x1u << 0) /**< \brief (HSMC_ELISR) Computation Terminated Interrupt Status */
#define HSMC_ELISR_ERR_CNT_Pos 8
#define HSMC_ELISR_ERR_CNT_Msk (0x3fu << HSMC_ELISR_ERR_CNT_Pos) /**< \brief (HSMC_ELISR) Error Counter value */
/* -------- HSMC_SIGMA0 : (SMC Offset: 0x528) PMECC Error Location SIGMA 0 Register -------- */
#define HSMC_SIGMA0_SIGMA0_Pos 0
#define HSMC_SIGMA0_SIGMA0_Msk (0x3fffu << HSMC_SIGMA0_SIGMA0_Pos) /**< \brief (HSMC_SIGMA0) Coefficient of degree 0 in the SIGMA polynomial */
/* -------- HSMC_SIGMA1 : (SMC Offset: 0x52C) PMECC Error Location SIGMA 1 Register -------- */
#define HSMC_SIGMA1_SIGMA1_Pos 0
#define HSMC_SIGMA1_SIGMA1_Msk (0x3fffu << HSMC_SIGMA1_SIGMA1_Pos) /**< \brief (HSMC_SIGMA1) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA1_SIGMA1(value) ((HSMC_SIGMA1_SIGMA1_Msk & ((value) << HSMC_SIGMA1_SIGMA1_Pos)))
/* -------- HSMC_SIGMA2 : (SMC Offset: 0x530) PMECC Error Location SIGMA 2 Register -------- */
#define HSMC_SIGMA2_SIGMA2_Pos 0
#define HSMC_SIGMA2_SIGMA2_Msk (0x3fffu << HSMC_SIGMA2_SIGMA2_Pos) /**< \brief (HSMC_SIGMA2) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA2_SIGMA2(value) ((HSMC_SIGMA2_SIGMA2_Msk & ((value) << HSMC_SIGMA2_SIGMA2_Pos)))
/* -------- HSMC_SIGMA3 : (SMC Offset: 0x534) PMECC Error Location SIGMA 3 Register -------- */
#define HSMC_SIGMA3_SIGMA3_Pos 0
#define HSMC_SIGMA3_SIGMA3_Msk (0x3fffu << HSMC_SIGMA3_SIGMA3_Pos) /**< \brief (HSMC_SIGMA3) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA3_SIGMA3(value) ((HSMC_SIGMA3_SIGMA3_Msk & ((value) << HSMC_SIGMA3_SIGMA3_Pos)))
/* -------- HSMC_SIGMA4 : (SMC Offset: 0x538) PMECC Error Location SIGMA 4 Register -------- */
#define HSMC_SIGMA4_SIGMA4_Pos 0
#define HSMC_SIGMA4_SIGMA4_Msk (0x3fffu << HSMC_SIGMA4_SIGMA4_Pos) /**< \brief (HSMC_SIGMA4) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA4_SIGMA4(value) ((HSMC_SIGMA4_SIGMA4_Msk & ((value) << HSMC_SIGMA4_SIGMA4_Pos)))
/* -------- HSMC_SIGMA5 : (SMC Offset: 0x53C) PMECC Error Location SIGMA 5 Register -------- */
#define HSMC_SIGMA5_SIGMA5_Pos 0
#define HSMC_SIGMA5_SIGMA5_Msk (0x3fffu << HSMC_SIGMA5_SIGMA5_Pos) /**< \brief (HSMC_SIGMA5) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA5_SIGMA5(value) ((HSMC_SIGMA5_SIGMA5_Msk & ((value) << HSMC_SIGMA5_SIGMA5_Pos)))
/* -------- HSMC_SIGMA6 : (SMC Offset: 0x540) PMECC Error Location SIGMA 6 Register -------- */
#define HSMC_SIGMA6_SIGMA6_Pos 0
#define HSMC_SIGMA6_SIGMA6_Msk (0x3fffu << HSMC_SIGMA6_SIGMA6_Pos) /**< \brief (HSMC_SIGMA6) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA6_SIGMA6(value) ((HSMC_SIGMA6_SIGMA6_Msk & ((value) << HSMC_SIGMA6_SIGMA6_Pos)))
/* -------- HSMC_SIGMA7 : (SMC Offset: 0x544) PMECC Error Location SIGMA 7 Register -------- */
#define HSMC_SIGMA7_SIGMA7_Pos 0
#define HSMC_SIGMA7_SIGMA7_Msk (0x3fffu << HSMC_SIGMA7_SIGMA7_Pos) /**< \brief (HSMC_SIGMA7) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA7_SIGMA7(value) ((HSMC_SIGMA7_SIGMA7_Msk & ((value) << HSMC_SIGMA7_SIGMA7_Pos)))
/* -------- HSMC_SIGMA8 : (SMC Offset: 0x548) PMECC Error Location SIGMA 8 Register -------- */
#define HSMC_SIGMA8_SIGMA8_Pos 0
#define HSMC_SIGMA8_SIGMA8_Msk (0x3fffu << HSMC_SIGMA8_SIGMA8_Pos) /**< \brief (HSMC_SIGMA8) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA8_SIGMA8(value) ((HSMC_SIGMA8_SIGMA8_Msk & ((value) << HSMC_SIGMA8_SIGMA8_Pos)))
/* -------- HSMC_SIGMA9 : (SMC Offset: 0x54C) PMECC Error Location SIGMA 9 Register -------- */
#define HSMC_SIGMA9_SIGMA9_Pos 0
#define HSMC_SIGMA9_SIGMA9_Msk (0x3fffu << HSMC_SIGMA9_SIGMA9_Pos) /**< \brief (HSMC_SIGMA9) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA9_SIGMA9(value) ((HSMC_SIGMA9_SIGMA9_Msk & ((value) << HSMC_SIGMA9_SIGMA9_Pos)))
/* -------- HSMC_SIGMA10 : (SMC Offset: 0x550) PMECC Error Location SIGMA 10 Register -------- */
#define HSMC_SIGMA10_SIGMA10_Pos 0
#define HSMC_SIGMA10_SIGMA10_Msk (0x3fffu << HSMC_SIGMA10_SIGMA10_Pos) /**< \brief (HSMC_SIGMA10) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA10_SIGMA10(value) ((HSMC_SIGMA10_SIGMA10_Msk & ((value) << HSMC_SIGMA10_SIGMA10_Pos)))
/* -------- HSMC_SIGMA11 : (SMC Offset: 0x554) PMECC Error Location SIGMA 11 Register -------- */
#define HSMC_SIGMA11_SIGMA11_Pos 0
#define HSMC_SIGMA11_SIGMA11_Msk (0x3fffu << HSMC_SIGMA11_SIGMA11_Pos) /**< \brief (HSMC_SIGMA11) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA11_SIGMA11(value) ((HSMC_SIGMA11_SIGMA11_Msk & ((value) << HSMC_SIGMA11_SIGMA11_Pos)))
/* -------- HSMC_SIGMA12 : (SMC Offset: 0x558) PMECC Error Location SIGMA 12 Register -------- */
#define HSMC_SIGMA12_SIGMA12_Pos 0
#define HSMC_SIGMA12_SIGMA12_Msk (0x3fffu << HSMC_SIGMA12_SIGMA12_Pos) /**< \brief (HSMC_SIGMA12) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA12_SIGMA12(value) ((HSMC_SIGMA12_SIGMA12_Msk & ((value) << HSMC_SIGMA12_SIGMA12_Pos)))
/* -------- HSMC_SIGMA13 : (SMC Offset: 0x55C) PMECC Error Location SIGMA 13 Register -------- */
#define HSMC_SIGMA13_SIGMA13_Pos 0
#define HSMC_SIGMA13_SIGMA13_Msk (0x3fffu << HSMC_SIGMA13_SIGMA13_Pos) /**< \brief (HSMC_SIGMA13) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA13_SIGMA13(value) ((HSMC_SIGMA13_SIGMA13_Msk & ((value) << HSMC_SIGMA13_SIGMA13_Pos)))
/* -------- HSMC_SIGMA14 : (SMC Offset: 0x560) PMECC Error Location SIGMA 14 Register -------- */
#define HSMC_SIGMA14_SIGMA14_Pos 0
#define HSMC_SIGMA14_SIGMA14_Msk (0x3fffu << HSMC_SIGMA14_SIGMA14_Pos) /**< \brief (HSMC_SIGMA14) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA14_SIGMA14(value) ((HSMC_SIGMA14_SIGMA14_Msk & ((value) << HSMC_SIGMA14_SIGMA14_Pos)))
/* -------- HSMC_SIGMA15 : (SMC Offset: 0x564) PMECC Error Location SIGMA 15 Register -------- */
#define HSMC_SIGMA15_SIGMA15_Pos 0
#define HSMC_SIGMA15_SIGMA15_Msk (0x3fffu << HSMC_SIGMA15_SIGMA15_Pos) /**< \brief (HSMC_SIGMA15) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA15_SIGMA15(value) ((HSMC_SIGMA15_SIGMA15_Msk & ((value) << HSMC_SIGMA15_SIGMA15_Pos)))
/* -------- HSMC_SIGMA16 : (SMC Offset: 0x568) PMECC Error Location SIGMA 16 Register -------- */
#define HSMC_SIGMA16_SIGMA16_Pos 0
#define HSMC_SIGMA16_SIGMA16_Msk (0x3fffu << HSMC_SIGMA16_SIGMA16_Pos) /**< \brief (HSMC_SIGMA16) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA16_SIGMA16(value) ((HSMC_SIGMA16_SIGMA16_Msk & ((value) << HSMC_SIGMA16_SIGMA16_Pos)))
/* -------- HSMC_SIGMA17 : (SMC Offset: 0x56C) PMECC Error Location SIGMA 17 Register -------- */
#define HSMC_SIGMA17_SIGMA17_Pos 0
#define HSMC_SIGMA17_SIGMA17_Msk (0x3fffu << HSMC_SIGMA17_SIGMA17_Pos) /**< \brief (HSMC_SIGMA17) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA17_SIGMA17(value) ((HSMC_SIGMA17_SIGMA17_Msk & ((value) << HSMC_SIGMA17_SIGMA17_Pos)))
/* -------- HSMC_SIGMA18 : (SMC Offset: 0x570) PMECC Error Location SIGMA 18 Register -------- */
#define HSMC_SIGMA18_SIGMA18_Pos 0
#define HSMC_SIGMA18_SIGMA18_Msk (0x3fffu << HSMC_SIGMA18_SIGMA18_Pos) /**< \brief (HSMC_SIGMA18) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA18_SIGMA18(value) ((HSMC_SIGMA18_SIGMA18_Msk & ((value) << HSMC_SIGMA18_SIGMA18_Pos)))
/* -------- HSMC_SIGMA19 : (SMC Offset: 0x574) PMECC Error Location SIGMA 19 Register -------- */
#define HSMC_SIGMA19_SIGMA19_Pos 0
#define HSMC_SIGMA19_SIGMA19_Msk (0x3fffu << HSMC_SIGMA19_SIGMA19_Pos) /**< \brief (HSMC_SIGMA19) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA19_SIGMA19(value) ((HSMC_SIGMA19_SIGMA19_Msk & ((value) << HSMC_SIGMA19_SIGMA19_Pos)))
/* -------- HSMC_SIGMA20 : (SMC Offset: 0x578) PMECC Error Location SIGMA 20 Register -------- */
#define HSMC_SIGMA20_SIGMA20_Pos 0
#define HSMC_SIGMA20_SIGMA20_Msk (0x3fffu << HSMC_SIGMA20_SIGMA20_Pos) /**< \brief (HSMC_SIGMA20) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA20_SIGMA20(value) ((HSMC_SIGMA20_SIGMA20_Msk & ((value) << HSMC_SIGMA20_SIGMA20_Pos)))
/* -------- HSMC_SIGMA21 : (SMC Offset: 0x57C) PMECC Error Location SIGMA 21 Register -------- */
#define HSMC_SIGMA21_SIGMA21_Pos 0
#define HSMC_SIGMA21_SIGMA21_Msk (0x3fffu << HSMC_SIGMA21_SIGMA21_Pos) /**< \brief (HSMC_SIGMA21) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA21_SIGMA21(value) ((HSMC_SIGMA21_SIGMA21_Msk & ((value) << HSMC_SIGMA21_SIGMA21_Pos)))
/* -------- HSMC_SIGMA22 : (SMC Offset: 0x580) PMECC Error Location SIGMA 22 Register -------- */
#define HSMC_SIGMA22_SIGMA22_Pos 0
#define HSMC_SIGMA22_SIGMA22_Msk (0x3fffu << HSMC_SIGMA22_SIGMA22_Pos) /**< \brief (HSMC_SIGMA22) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA22_SIGMA22(value) ((HSMC_SIGMA22_SIGMA22_Msk & ((value) << HSMC_SIGMA22_SIGMA22_Pos)))
/* -------- HSMC_SIGMA23 : (SMC Offset: 0x584) PMECC Error Location SIGMA 23 Register -------- */
#define HSMC_SIGMA23_SIGMA23_Pos 0
#define HSMC_SIGMA23_SIGMA23_Msk (0x3fffu << HSMC_SIGMA23_SIGMA23_Pos) /**< \brief (HSMC_SIGMA23) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA23_SIGMA23(value) ((HSMC_SIGMA23_SIGMA23_Msk & ((value) << HSMC_SIGMA23_SIGMA23_Pos)))
/* -------- HSMC_SIGMA24 : (SMC Offset: 0x588) PMECC Error Location SIGMA 24 Register -------- */
#define HSMC_SIGMA24_SIGMA24_Pos 0
#define HSMC_SIGMA24_SIGMA24_Msk (0x3fffu << HSMC_SIGMA24_SIGMA24_Pos) /**< \brief (HSMC_SIGMA24) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA24_SIGMA24(value) ((HSMC_SIGMA24_SIGMA24_Msk & ((value) << HSMC_SIGMA24_SIGMA24_Pos)))
/* -------- HSMC_SIGMA25 : (SMC Offset: 0x58C) PMECC Error Location SIGMA 25 Register -------- */
#define HSMC_SIGMA25_SIGMA25_Pos 0
#define HSMC_SIGMA25_SIGMA25_Msk (0x3fffu << HSMC_SIGMA25_SIGMA25_Pos) /**< \brief (HSMC_SIGMA25) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA25_SIGMA25(value) ((HSMC_SIGMA25_SIGMA25_Msk & ((value) << HSMC_SIGMA25_SIGMA25_Pos)))
/* -------- HSMC_SIGMA26 : (SMC Offset: 0x590) PMECC Error Location SIGMA 26 Register -------- */
#define HSMC_SIGMA26_SIGMA26_Pos 0
#define HSMC_SIGMA26_SIGMA26_Msk (0x3fffu << HSMC_SIGMA26_SIGMA26_Pos) /**< \brief (HSMC_SIGMA26) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA26_SIGMA26(value) ((HSMC_SIGMA26_SIGMA26_Msk & ((value) << HSMC_SIGMA26_SIGMA26_Pos)))
/* -------- HSMC_SIGMA27 : (SMC Offset: 0x594) PMECC Error Location SIGMA 27 Register -------- */
#define HSMC_SIGMA27_SIGMA27_Pos 0
#define HSMC_SIGMA27_SIGMA27_Msk (0x3fffu << HSMC_SIGMA27_SIGMA27_Pos) /**< \brief (HSMC_SIGMA27) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA27_SIGMA27(value) ((HSMC_SIGMA27_SIGMA27_Msk & ((value) << HSMC_SIGMA27_SIGMA27_Pos)))
/* -------- HSMC_SIGMA28 : (SMC Offset: 0x598) PMECC Error Location SIGMA 28 Register -------- */
#define HSMC_SIGMA28_SIGMA28_Pos 0
#define HSMC_SIGMA28_SIGMA28_Msk (0x3fffu << HSMC_SIGMA28_SIGMA28_Pos) /**< \brief (HSMC_SIGMA28) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA28_SIGMA28(value) ((HSMC_SIGMA28_SIGMA28_Msk & ((value) << HSMC_SIGMA28_SIGMA28_Pos)))
/* -------- HSMC_SIGMA29 : (SMC Offset: 0x59C) PMECC Error Location SIGMA 29 Register -------- */
#define HSMC_SIGMA29_SIGMA29_Pos 0
#define HSMC_SIGMA29_SIGMA29_Msk (0x3fffu << HSMC_SIGMA29_SIGMA29_Pos) /**< \brief (HSMC_SIGMA29) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA29_SIGMA29(value) ((HSMC_SIGMA29_SIGMA29_Msk & ((value) << HSMC_SIGMA29_SIGMA29_Pos)))
/* -------- HSMC_SIGMA30 : (SMC Offset: 0x5A0) PMECC Error Location SIGMA 30 Register -------- */
#define HSMC_SIGMA30_SIGMA30_Pos 0
#define HSMC_SIGMA30_SIGMA30_Msk (0x3fffu << HSMC_SIGMA30_SIGMA30_Pos) /**< \brief (HSMC_SIGMA30) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA30_SIGMA30(value) ((HSMC_SIGMA30_SIGMA30_Msk & ((value) << HSMC_SIGMA30_SIGMA30_Pos)))
/* -------- HSMC_SIGMA31 : (SMC Offset: 0x5A4) PMECC Error Location SIGMA 31 Register -------- */
#define HSMC_SIGMA31_SIGMA31_Pos 0
#define HSMC_SIGMA31_SIGMA31_Msk (0x3fffu << HSMC_SIGMA31_SIGMA31_Pos) /**< \brief (HSMC_SIGMA31) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA31_SIGMA31(value) ((HSMC_SIGMA31_SIGMA31_Msk & ((value) << HSMC_SIGMA31_SIGMA31_Pos)))
/* -------- HSMC_SIGMA32 : (SMC Offset: 0x5A8) PMECC Error Location SIGMA 32 Register -------- */
#define HSMC_SIGMA32_SIGMA32_Pos 0
#define HSMC_SIGMA32_SIGMA32_Msk (0x3fffu << HSMC_SIGMA32_SIGMA32_Pos) /**< \brief (HSMC_SIGMA32) Coefficient of degree x in the SIGMA polynomial */
#define HSMC_SIGMA32_SIGMA32(value) ((HSMC_SIGMA32_SIGMA32_Msk & ((value) << HSMC_SIGMA32_SIGMA32_Pos)))
/* -------- HSMC_ERRLOC0 : (SMC Offset: 0x5AC) PMECC Error Location 0 Register -------- */
#define HSMC_ERRLOC0_ERRLOCN_Pos 0
#define HSMC_ERRLOC0_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC0_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC0) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC1 : (SMC Offset: 0x5B0) PMECC Error Location 1 Register -------- */
#define HSMC_ERRLOC1_ERRLOCN_Pos 0
#define HSMC_ERRLOC1_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC1_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC1) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC2 : (SMC Offset: 0x5B4) PMECC Error Location 2 Register -------- */
#define HSMC_ERRLOC2_ERRLOCN_Pos 0
#define HSMC_ERRLOC2_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC2_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC2) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC3 : (SMC Offset: 0x5B8) PMECC Error Location 3 Register -------- */
#define HSMC_ERRLOC3_ERRLOCN_Pos 0
#define HSMC_ERRLOC3_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC3_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC3) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC4 : (SMC Offset: 0x5BC) PMECC Error Location 4 Register -------- */
#define HSMC_ERRLOC4_ERRLOCN_Pos 0
#define HSMC_ERRLOC4_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC4_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC4) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC5 : (SMC Offset: 0x5C0) PMECC Error Location 5 Register -------- */
#define HSMC_ERRLOC5_ERRLOCN_Pos 0
#define HSMC_ERRLOC5_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC5_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC5) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC6 : (SMC Offset: 0x5C4) PMECC Error Location 6 Register -------- */
#define HSMC_ERRLOC6_ERRLOCN_Pos 0
#define HSMC_ERRLOC6_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC6_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC6) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC7 : (SMC Offset: 0x5C8) PMECC Error Location 7 Register -------- */
#define HSMC_ERRLOC7_ERRLOCN_Pos 0
#define HSMC_ERRLOC7_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC7_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC7) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC8 : (SMC Offset: 0x5CC) PMECC Error Location 8 Register -------- */
#define HSMC_ERRLOC8_ERRLOCN_Pos 0
#define HSMC_ERRLOC8_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC8_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC8) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC9 : (SMC Offset: 0x5D0) PMECC Error Location 9 Register -------- */
#define HSMC_ERRLOC9_ERRLOCN_Pos 0
#define HSMC_ERRLOC9_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC9_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC9) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC10 : (SMC Offset: 0x5D4) PMECC Error Location 10 Register -------- */
#define HSMC_ERRLOC10_ERRLOCN_Pos 0
#define HSMC_ERRLOC10_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC10_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC10) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC11 : (SMC Offset: 0x5D8) PMECC Error Location 11 Register -------- */
#define HSMC_ERRLOC11_ERRLOCN_Pos 0
#define HSMC_ERRLOC11_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC11_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC11) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC12 : (SMC Offset: 0x5DC) PMECC Error Location 12 Register -------- */
#define HSMC_ERRLOC12_ERRLOCN_Pos 0
#define HSMC_ERRLOC12_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC12_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC12) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC13 : (SMC Offset: 0x5E0) PMECC Error Location 13 Register -------- */
#define HSMC_ERRLOC13_ERRLOCN_Pos 0
#define HSMC_ERRLOC13_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC13_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC13) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC14 : (SMC Offset: 0x5E4) PMECC Error Location 14 Register -------- */
#define HSMC_ERRLOC14_ERRLOCN_Pos 0
#define HSMC_ERRLOC14_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC14_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC14) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC15 : (SMC Offset: 0x5E8) PMECC Error Location 15 Register -------- */
#define HSMC_ERRLOC15_ERRLOCN_Pos 0
#define HSMC_ERRLOC15_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC15_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC15) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC16 : (SMC Offset: 0x5EC) PMECC Error Location 16 Register -------- */
#define HSMC_ERRLOC16_ERRLOCN_Pos 0
#define HSMC_ERRLOC16_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC16_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC16) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC17 : (SMC Offset: 0x5F0) PMECC Error Location 17 Register -------- */
#define HSMC_ERRLOC17_ERRLOCN_Pos 0
#define HSMC_ERRLOC17_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC17_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC17) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC18 : (SMC Offset: 0x5F4) PMECC Error Location 18 Register -------- */
#define HSMC_ERRLOC18_ERRLOCN_Pos 0
#define HSMC_ERRLOC18_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC18_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC18) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC19 : (SMC Offset: 0x5F8) PMECC Error Location 19 Register -------- */
#define HSMC_ERRLOC19_ERRLOCN_Pos 0
#define HSMC_ERRLOC19_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC19_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC19) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC20 : (SMC Offset: 0x5FC) PMECC Error Location 20 Register -------- */
#define HSMC_ERRLOC20_ERRLOCN_Pos 0
#define HSMC_ERRLOC20_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC20_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC20) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC21 : (SMC Offset: 0x600) PMECC Error Location 21 Register -------- */
#define HSMC_ERRLOC21_ERRLOCN_Pos 0
#define HSMC_ERRLOC21_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC21_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC21) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC22 : (SMC Offset: 0x604) PMECC Error Location 22 Register -------- */
#define HSMC_ERRLOC22_ERRLOCN_Pos 0
#define HSMC_ERRLOC22_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC22_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC22) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_ERRLOC23 : (SMC Offset: 0x608) PMECC Error Location 23 Register -------- */
#define HSMC_ERRLOC23_ERRLOCN_Pos 0
#define HSMC_ERRLOC23_ERRLOCN_Msk (0x3fffu << HSMC_ERRLOC23_ERRLOCN_Pos) /**< \brief (HSMC_ERRLOC23) Error Position within the Set {sector area, spare area} */
/* -------- HSMC_SETUP : (SMC Offset: N/A) HSMC Setup Register -------- */
#define HSMC_SETUP_NWE_SETUP_Pos 0
#define HSMC_SETUP_NWE_SETUP_Msk (0x3fu << HSMC_SETUP_NWE_SETUP_Pos) /**< \brief (HSMC_SETUP) NWE Setup Length */
#define HSMC_SETUP_NWE_SETUP(value) ((HSMC_SETUP_NWE_SETUP_Msk & ((value) << HSMC_SETUP_NWE_SETUP_Pos)))
#define HSMC_SETUP_NCS_WR_SETUP_Pos 8
#define HSMC_SETUP_NCS_WR_SETUP_Msk (0x3fu << HSMC_SETUP_NCS_WR_SETUP_Pos) /**< \brief (HSMC_SETUP) NCS Setup Length in Write Access */
#define HSMC_SETUP_NCS_WR_SETUP(value) ((HSMC_SETUP_NCS_WR_SETUP_Msk & ((value) << HSMC_SETUP_NCS_WR_SETUP_Pos)))
#define HSMC_SETUP_NRD_SETUP_Pos 16
#define HSMC_SETUP_NRD_SETUP_Msk (0x3fu << HSMC_SETUP_NRD_SETUP_Pos) /**< \brief (HSMC_SETUP) NRD Setup Length */
#define HSMC_SETUP_NRD_SETUP(value) ((HSMC_SETUP_NRD_SETUP_Msk & ((value) << HSMC_SETUP_NRD_SETUP_Pos)))
#define HSMC_SETUP_NCS_RD_SETUP_Pos 24
#define HSMC_SETUP_NCS_RD_SETUP_Msk (0x3fu << HSMC_SETUP_NCS_RD_SETUP_Pos) /**< \brief (HSMC_SETUP) NCS Setup Length in Read Access */
#define HSMC_SETUP_NCS_RD_SETUP(value) ((HSMC_SETUP_NCS_RD_SETUP_Msk & ((value) << HSMC_SETUP_NCS_RD_SETUP_Pos)))
/* -------- HSMC_PULSE : (SMC Offset: N/A) HSMC Pulse Register -------- */
#define HSMC_PULSE_NWE_PULSE_Pos 0
#define HSMC_PULSE_NWE_PULSE_Msk (0x7fu << HSMC_PULSE_NWE_PULSE_Pos) /**< \brief (HSMC_PULSE) NWE Pulse Length */
#define HSMC_PULSE_NWE_PULSE(value) ((HSMC_PULSE_NWE_PULSE_Msk & ((value) << HSMC_PULSE_NWE_PULSE_Pos)))
#define HSMC_PULSE_NCS_WR_PULSE_Pos 8
#define HSMC_PULSE_NCS_WR_PULSE_Msk (0x7fu << HSMC_PULSE_NCS_WR_PULSE_Pos) /**< \brief (HSMC_PULSE) NCS Pulse Length in WRITE Access */
#define HSMC_PULSE_NCS_WR_PULSE(value) ((HSMC_PULSE_NCS_WR_PULSE_Msk & ((value) << HSMC_PULSE_NCS_WR_PULSE_Pos)))
#define HSMC_PULSE_NRD_PULSE_Pos 16
#define HSMC_PULSE_NRD_PULSE_Msk (0x7fu << HSMC_PULSE_NRD_PULSE_Pos) /**< \brief (HSMC_PULSE) NRD Pulse Length */
#define HSMC_PULSE_NRD_PULSE(value) ((HSMC_PULSE_NRD_PULSE_Msk & ((value) << HSMC_PULSE_NRD_PULSE_Pos)))
#define HSMC_PULSE_NCS_RD_PULSE_Pos 24
#define HSMC_PULSE_NCS_RD_PULSE_Msk (0x7fu << HSMC_PULSE_NCS_RD_PULSE_Pos) /**< \brief (HSMC_PULSE) NCS Pulse Length in READ Access */
#define HSMC_PULSE_NCS_RD_PULSE(value) ((HSMC_PULSE_NCS_RD_PULSE_Msk & ((value) << HSMC_PULSE_NCS_RD_PULSE_Pos)))
/* -------- HSMC_CYCLE : (SMC Offset: N/A) HSMC Cycle Register -------- */
#define HSMC_CYCLE_NWE_CYCLE_Pos 0
#define HSMC_CYCLE_NWE_CYCLE_Msk (0x1ffu << HSMC_CYCLE_NWE_CYCLE_Pos) /**< \brief (HSMC_CYCLE) Total Write Cycle Length */
#define HSMC_CYCLE_NWE_CYCLE(value) ((HSMC_CYCLE_NWE_CYCLE_Msk & ((value) << HSMC_CYCLE_NWE_CYCLE_Pos)))
#define HSMC_CYCLE_NRD_CYCLE_Pos 16
#define HSMC_CYCLE_NRD_CYCLE_Msk (0x1ffu << HSMC_CYCLE_NRD_CYCLE_Pos) /**< \brief (HSMC_CYCLE) Total Read Cycle Length */
#define HSMC_CYCLE_NRD_CYCLE(value) ((HSMC_CYCLE_NRD_CYCLE_Msk & ((value) << HSMC_CYCLE_NRD_CYCLE_Pos)))
/* -------- HSMC_TIMINGS : (SMC Offset: N/A) HSMC Timings Register -------- */
#define HSMC_TIMINGS_TCLR_Pos 0
#define HSMC_TIMINGS_TCLR_Msk (0xfu << HSMC_TIMINGS_TCLR_Pos) /**< \brief (HSMC_TIMINGS) CLE to REN Low Delay */
#define HSMC_TIMINGS_TCLR(value) ((HSMC_TIMINGS_TCLR_Msk & ((value) << HSMC_TIMINGS_TCLR_Pos)))
#define HSMC_TIMINGS_TADL_Pos 4
#define HSMC_TIMINGS_TADL_Msk (0xfu << HSMC_TIMINGS_TADL_Pos) /**< \brief (HSMC_TIMINGS) ALE to Data Start */
#define HSMC_TIMINGS_TADL(value) ((HSMC_TIMINGS_TADL_Msk & ((value) << HSMC_TIMINGS_TADL_Pos)))
#define HSMC_TIMINGS_TAR_Pos 8
#define HSMC_TIMINGS_TAR_Msk (0xfu << HSMC_TIMINGS_TAR_Pos) /**< \brief (HSMC_TIMINGS) ALE to REN Low Delay */
#define HSMC_TIMINGS_TAR(value) ((HSMC_TIMINGS_TAR_Msk & ((value) << HSMC_TIMINGS_TAR_Pos)))
#define HSMC_TIMINGS_OCMS (0x1u << 12) /**< \brief (HSMC_TIMINGS) Off Chip Memory Scrambling Enable */
#define HSMC_TIMINGS_TRR_Pos 16
#define HSMC_TIMINGS_TRR_Msk (0xfu << HSMC_TIMINGS_TRR_Pos) /**< \brief (HSMC_TIMINGS) Ready to REN Low Delay */
#define HSMC_TIMINGS_TRR(value) ((HSMC_TIMINGS_TRR_Msk & ((value) << HSMC_TIMINGS_TRR_Pos)))
#define HSMC_TIMINGS_TWB_Pos 24
#define HSMC_TIMINGS_TWB_Msk (0xfu << HSMC_TIMINGS_TWB_Pos) /**< \brief (HSMC_TIMINGS) WEN High to REN to Busy */
#define HSMC_TIMINGS_TWB(value) ((HSMC_TIMINGS_TWB_Msk & ((value) << HSMC_TIMINGS_TWB_Pos)))
#define HSMC_TIMINGS_RBNSEL_Pos 28
#define HSMC_TIMINGS_RBNSEL_Msk (0x7u << HSMC_TIMINGS_RBNSEL_Pos) /**< \brief (HSMC_TIMINGS) Ready/Busy Line Selection */
#define HSMC_TIMINGS_RBNSEL(value) ((HSMC_TIMINGS_RBNSEL_Msk & ((value) << HSMC_TIMINGS_RBNSEL_Pos)))
#define HSMC_TIMINGS_NFSEL (0x1u << 31) /**< \brief (HSMC_TIMINGS) NAND Flash Selection */
/* -------- HSMC_MODE : (SMC Offset: N/A) HSMC Mode Register -------- */
#define HSMC_MODE_READ_MODE (0x1u << 0) /**< \brief (HSMC_MODE) Selection of the Control Signal for Read Operation */
#define   HSMC_MODE_READ_MODE_NCS_CTRL (0x0u << 0) /**< \brief (HSMC_MODE) The Read operation is controlled by the NCS signal. */
#define   HSMC_MODE_READ_MODE_NRD_CTRL (0x1u << 0) /**< \brief (HSMC_MODE) The Read operation is controlled by the NRD signal. */
#define HSMC_MODE_WRITE_MODE (0x1u << 1) /**< \brief (HSMC_MODE) Selection of the Control Signal for Write Operation */
#define   HSMC_MODE_WRITE_MODE_NCS_CTRL (0x0u << 1) /**< \brief (HSMC_MODE) The Write operation is controller by the NCS signal. */
#define   HSMC_MODE_WRITE_MODE_NWE_CTRL (0x1u << 1) /**< \brief (HSMC_MODE) The Write operation is controlled by the NWE signal */
#define HSMC_MODE_EXNW_MODE_Pos 4
#define HSMC_MODE_EXNW_MODE_Msk (0x3u << HSMC_MODE_EXNW_MODE_Pos) /**< \brief (HSMC_MODE) NWAIT Mode */
#define HSMC_MODE_EXNW_MODE(value) ((HSMC_MODE_EXNW_MODE_Msk & ((value) << HSMC_MODE_EXNW_MODE_Pos)))
#define   HSMC_MODE_EXNW_MODE_DISABLED (0x0u << 4) /**< \brief (HSMC_MODE) Disabled-The NWAIT input signal is ignored on the corresponding Chip Select. */
#define   HSMC_MODE_EXNW_MODE_FROZEN (0x2u << 4) /**< \brief (HSMC_MODE) Frozen Mode-If asserted, the NWAIT signal freezes the current read or write cycle. After deassertion, the read/write cycle is resumed from the point where it was stopped. */
#define   HSMC_MODE_EXNW_MODE_READY (0x3u << 4) /**< \brief (HSMC_MODE) Ready Mode-The NWAIT signal indicates the availability of the external device at the end of the pulse of the controlling read or write signal, to complete the access. If high, the access normally completes. If low, the access is extended until NWAIT returns high. */
#define HSMC_MODE_BAT (0x1u << 8) /**< \brief (HSMC_MODE) Byte Access Type */
#define   HSMC_MODE_BAT_BYTE_SELECT (0x0u << 8) /**< \brief (HSMC_MODE) Byte select access type:- Write operation is controlled using NCS, NWE, NBS0, NBS1.- Read operation is controlled using NCS, NRD, NBS0, NBS1. */
#define   HSMC_MODE_BAT_BYTE_WRITE (0x1u << 8) /**< \brief (HSMC_MODE) Byte write access type:- Write operation is controlled using NCS, NWR0, NWR1.- Read operation is controlled using NCS and NRD. */
#define HSMC_MODE_DBW (0x1u << 12) /**< \brief (HSMC_MODE) Data Bus Width */
#define   HSMC_MODE_DBW_BIT_8 (0x0u << 12) /**< \brief (HSMC_MODE) 8-bit bus */
#define   HSMC_MODE_DBW_BIT_16 (0x1u << 12) /**< \brief (HSMC_MODE) 16-bit bus */
#define HSMC_MODE_TDF_CYCLES_Pos 16
#define HSMC_MODE_TDF_CYCLES_Msk (0xfu << HSMC_MODE_TDF_CYCLES_Pos) /**< \brief (HSMC_MODE) Data Float Time */
#define HSMC_MODE_TDF_CYCLES(value) ((HSMC_MODE_TDF_CYCLES_Msk & ((value) << HSMC_MODE_TDF_CYCLES_Pos)))
#define HSMC_MODE_TDF_MODE (0x1u << 20) /**< \brief (HSMC_MODE) TDF Optimization */
/* -------- HSMC_OCMS : (SMC Offset: 0x7A0) HSMC Off Chip Memory Scrambling Register -------- */
#define HSMC_OCMS_SMSE (0x1u << 0) /**< \brief (HSMC_OCMS) Static Memory Controller Scrambling Enable */
#define HSMC_OCMS_SRSE (0x1u << 1) /**< \brief (HSMC_OCMS) NFC Internal SRAM Scrambling Enable */
/* -------- HSMC_KEY1 : (SMC Offset: 0x7A4) HSMC Off Chip Memory Scrambling KEY1 Register -------- */
#define HSMC_KEY1_KEY1_Pos 0
#define HSMC_KEY1_KEY1_Msk (0xffffffffu << HSMC_KEY1_KEY1_Pos) /**< \brief (HSMC_KEY1) Off Chip Memory Scrambling (OCMS) Key Part 1 */
#define HSMC_KEY1_KEY1(value) ((HSMC_KEY1_KEY1_Msk & ((value) << HSMC_KEY1_KEY1_Pos)))
/* -------- HSMC_KEY2 : (SMC Offset: 0x7A8) HSMC Off Chip Memory Scrambling KEY2 Register -------- */
#define HSMC_KEY2_KEY2_Pos 0
#define HSMC_KEY2_KEY2_Msk (0xffffffffu << HSMC_KEY2_KEY2_Pos) /**< \brief (HSMC_KEY2) Off Chip Memory Scrambling (OCMS) Key Part 2 */
#define HSMC_KEY2_KEY2(value) ((HSMC_KEY2_KEY2_Msk & ((value) << HSMC_KEY2_KEY2_Pos)))
/* -------- HSMC_WPMR : (SMC Offset: 0x7E4) HSMC Write Protection Mode Register -------- */
#define HSMC_WPMR_WPEN (0x1u << 0) /**< \brief (HSMC_WPMR) Write Protection Enable */
#define HSMC_WPMR_WPKEY_Pos 8
#define HSMC_WPMR_WPKEY_Msk (0xffffffu << HSMC_WPMR_WPKEY_Pos) /**< \brief (HSMC_WPMR) Write Protection Key */
#define HSMC_WPMR_WPKEY(value) ((HSMC_WPMR_WPKEY_Msk & ((value) << HSMC_WPMR_WPKEY_Pos)))
#define   HSMC_WPMR_WPKEY_PASSWD (0x534D43u << 8) /**< \brief (HSMC_WPMR) Writing any other value in this field aborts the write operation of bit WPEN.Always reads as 0. */
/* -------- HSMC_WPSR : (SMC Offset: 0x7E8) HSMC Write Protection Status Register -------- */
#define HSMC_WPSR_WPVS (0x1u << 0) /**< \brief (HSMC_WPSR) Write Protection Violation Status */
#define HSMC_WPSR_WPVSRC_Pos 8
#define HSMC_WPSR_WPVSRC_Msk (0xffffu << HSMC_WPSR_WPVSRC_Pos) /**< \brief (HSMC_WPSR) Write Protection Violation Source */
/* -------- HSMC_VERSION : (SMC Offset: 0x7FC) HSMC Version Register -------- */
#define HSMC_VERSION_VERSION_Pos 0
#define HSMC_VERSION_VERSION_Msk (0xfffu << HSMC_VERSION_VERSION_Pos) /**< \brief (HSMC_VERSION) Hardware Version Number */
#define HSMC_VERSION_MFN_Pos 16
#define HSMC_VERSION_MFN_Msk (0x7u << HSMC_VERSION_MFN_Pos) /**< \brief (HSMC_VERSION) Metal Fix Number */

/*@}*/


#endif /* _SAMA5D2_SMC_COMPONENT_ */
