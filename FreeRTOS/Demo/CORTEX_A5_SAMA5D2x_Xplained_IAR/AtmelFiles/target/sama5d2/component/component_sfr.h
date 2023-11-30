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

#ifndef _SAMA5D2_SFR_COMPONENT_
#define _SAMA5D2_SFR_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Special Function Registers */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SFR Special Function Registers */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sfr hardware registers */
typedef struct {
  __I  uint32_t Reserved0[1];
  __IO uint32_t SFR_DDRCFG;     /**< \brief (Sfr Offset: 0x04) DDR Configuration Register */
  __I  uint32_t Reserved1[2];
  __IO uint32_t SFR_OHCIICR;    /**< \brief (Sfr Offset: 0x10) OHCI Interrupt Configuration Register */
  __I  uint32_t SFR_OHCIISR;    /**< \brief (Sfr Offset: 0x14) OHCI Interrupt Status Register */
  __I  uint32_t Reserved2[4];
  __IO uint32_t SFR_SECURE;     /**< \brief (Sfr Offset: 0x28) Security Configuration Register */
  __I  uint32_t Reserved3[1];
  __IO uint32_t SFR_UTMICKTRIM; /**< \brief (Sfr Offset: 0x30) UTMI Clock Trimming Register */
  __IO uint32_t SFR_UTMIHSTRIM; /**< \brief (Sfr Offset: 0x34) UTMI High Speed Trimming Register */
  __IO uint32_t SFR_UTMIFSTRIM; /**< \brief (Sfr Offset: 0x38) UTMI Full Speed Trimming Register */
  __IO uint32_t SFR_UTMISWAP;   /**< \brief (Sfr Offset: 0x3C) UTMI DP/DM Pin Swapping Register */
  __IO uint32_t SFR_EBICFG;     /**< \brief (Sfr Offset: 0x40) EBI Configuration Register */
  __I  uint32_t Reserved4[1];
  __IO uint32_t SFR_CAN;        /**< \brief (Sfr Offset: 0x48) CAN Memories Address-based Register */
  __I  uint32_t SFR_SN0;        /**< \brief (Sfr Offset: 0x4C) Serial Number 0 Register */
  __I  uint32_t SFR_SN1;        /**< \brief (Sfr Offset: 0x50) Serial Number 1 Register */
  __IO uint32_t SFR_AICREDIR;   /**< \brief (Sfr Offset: 0x54) AIC interrupt Redirection Register */
  __IO uint32_t SFR_L2CC_HRAMC; /**< \brief (Sfr Offset: 0x58) L2CC_HRAMC1 */
  __I  uint32_t Reserved5[13];
  __IO uint32_t SFR_I2SCLKSEL;  /**< \brief (Sfr Offset: 0x90) I2SC Register */
  __IO uint32_t QSPICLK_REG;    /**< \brief (Sfr Offset: 0x94) QSPI Clock Pad Supply Select Register */
} Sfr;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SFR_DDRCFG : (SFR Offset: 0x04) DDR Configuration Register -------- */
#define SFR_DDRCFG_FDQIEN (0x1u << 16) /**< \brief (SFR_DDRCFG) Force DDR_DQ Input Buffer Always On */
#define SFR_DDRCFG_FDQSIEN (0x1u << 17) /**< \brief (SFR_DDRCFG) Force DDR_DQS Input Buffer Always On */
/* -------- SFR_OHCIICR : (SFR Offset: 0x10) OHCI Interrupt Configuration Register -------- */
#define SFR_OHCIICR_RES0 (0x1u << 0) /**< \brief (SFR_OHCIICR) USB PORTx RESET */
#define SFR_OHCIICR_RES1 (0x1u << 1) /**< \brief (SFR_OHCIICR) USB PORTx RESET */
#define SFR_OHCIICR_RES2 (0x1u << 2) /**< \brief (SFR_OHCIICR) USB PORTx RESET */
#define SFR_OHCIICR_ARIE (0x1u << 4) /**< \brief (SFR_OHCIICR) OHCI Asynchronous Resume Interrupt Enable */
#define SFR_OHCIICR_APPSTART (0x1u << 5) /**< \brief (SFR_OHCIICR) Reserved */
#define SFR_OHCIICR_SUSPEND_A (0x1u << 8) /**< \brief (SFR_OHCIICR) USB PORT A */
#define SFR_OHCIICR_SUSPEND_B (0x1u << 9) /**< \brief (SFR_OHCIICR) USB PORT B */
#define SFR_OHCIICR_SUSPEND_C (0x1u << 10) /**< \brief (SFR_OHCIICR) USB PORT C */
#define SFR_OHCIICR_UDPPUDIS (0x1u << 23) /**< \brief (SFR_OHCIICR) USB DEVICE PULL-UP DISABLE */
#define SFR_OHCIICR_HSIC_SEL (0x1u << 27) /**< \brief (SFR_OHCIICR) Reserved */
/* -------- SFR_OHCIISR : (SFR Offset: 0x14) OHCI Interrupt Status Register -------- */
#define SFR_OHCIISR_RIS0 (0x1u << 0) /**< \brief (SFR_OHCIISR) OHCI Resume Interrupt Status Port 0 */
#define SFR_OHCIISR_RIS1 (0x1u << 1) /**< \brief (SFR_OHCIISR) OHCI Resume Interrupt Status Port 1 */
#define SFR_OHCIISR_RIS2 (0x1u << 2) /**< \brief (SFR_OHCIISR) OHCI Resume Interrupt Status Port 2 */
/* -------- SFR_SECURE : (SFR Offset: 0x28) Security Configuration Register -------- */
#define SFR_SECURE_ROM (0x1u << 0) /**< \brief (SFR_SECURE) Disable Access to ROM Code */
#define SFR_SECURE_FUSE (0x1u << 8) /**< \brief (SFR_SECURE) Disable Access to Fuse Controller */
/* -------- SFR_UTMICKTRIM : (SFR Offset: 0x30) UTMI Clock Trimming Register -------- */
#define SFR_UTMICKTRIM_FREQ_Pos 0
#define SFR_UTMICKTRIM_FREQ_Msk (0x3u << SFR_UTMICKTRIM_FREQ_Pos) /**< \brief (SFR_UTMICKTRIM) UTMI Reference Clock Frequency */
#define SFR_UTMICKTRIM_FREQ(value) ((SFR_UTMICKTRIM_FREQ_Msk & ((value) << SFR_UTMICKTRIM_FREQ_Pos)))
#define   SFR_UTMICKTRIM_FREQ_12 (0x0u << 0) /**< \brief (SFR_UTMICKTRIM) 12 MHz reference clock */
#define   SFR_UTMICKTRIM_FREQ_16 (0x1u << 0) /**< \brief (SFR_UTMICKTRIM) 16 MHz reference clock */
#define   SFR_UTMICKTRIM_FREQ_24 (0x2u << 0) /**< \brief (SFR_UTMICKTRIM) 24 MHz reference clock */
#define SFR_UTMICKTRIM_VBG_Pos 16
#define SFR_UTMICKTRIM_VBG_Msk (0xfu << SFR_UTMICKTRIM_VBG_Pos) /**< \brief (SFR_UTMICKTRIM) UTMI Band Gap Voltage Trimming */
#define SFR_UTMICKTRIM_VBG(value) ((SFR_UTMICKTRIM_VBG_Msk & ((value) << SFR_UTMICKTRIM_VBG_Pos)))
/* -------- SFR_UTMIHSTRIM : (SFR Offset: 0x34) UTMI High Speed Trimming Register -------- */
#define SFR_UTMIHSTRIM_SQUELCH_Pos 0
#define SFR_UTMIHSTRIM_SQUELCH_Msk (0x7u << SFR_UTMIHSTRIM_SQUELCH_Pos) /**< \brief (SFR_UTMIHSTRIM) UTMI HS SQUELCH Voltage Trimming */
#define SFR_UTMIHSTRIM_SQUELCH(value) ((SFR_UTMIHSTRIM_SQUELCH_Msk & ((value) << SFR_UTMIHSTRIM_SQUELCH_Pos)))
#define SFR_UTMIHSTRIM_DISC_Pos 4
#define SFR_UTMIHSTRIM_DISC_Msk (0x7u << SFR_UTMIHSTRIM_DISC_Pos) /**< \brief (SFR_UTMIHSTRIM) UTMI Disconnect Voltage Trimming */
#define SFR_UTMIHSTRIM_DISC(value) ((SFR_UTMIHSTRIM_DISC_Msk & ((value) << SFR_UTMIHSTRIM_DISC_Pos)))
#define SFR_UTMIHSTRIM_SLOPE0_Pos 8
#define SFR_UTMIHSTRIM_SLOPE0_Msk (0x7u << SFR_UTMIHSTRIM_SLOPE0_Pos) /**< \brief (SFR_UTMIHSTRIM) UTMI HS PORTx Transceiver Slope Trimming */
#define SFR_UTMIHSTRIM_SLOPE0(value) ((SFR_UTMIHSTRIM_SLOPE0_Msk & ((value) << SFR_UTMIHSTRIM_SLOPE0_Pos)))
#define SFR_UTMIHSTRIM_SLOPE1_Pos 12
#define SFR_UTMIHSTRIM_SLOPE1_Msk (0x7u << SFR_UTMIHSTRIM_SLOPE1_Pos) /**< \brief (SFR_UTMIHSTRIM) UTMI HS PORTx Transceiver Slope Trimming */
#define SFR_UTMIHSTRIM_SLOPE1(value) ((SFR_UTMIHSTRIM_SLOPE1_Msk & ((value) << SFR_UTMIHSTRIM_SLOPE1_Pos)))
#define SFR_UTMIHSTRIM_SLOPE2_Pos 16
#define SFR_UTMIHSTRIM_SLOPE2_Msk (0x7u << SFR_UTMIHSTRIM_SLOPE2_Pos) /**< \brief (SFR_UTMIHSTRIM) UTMI HS PORTx Transceiver Slope Trimming */
#define SFR_UTMIHSTRIM_SLOPE2(value) ((SFR_UTMIHSTRIM_SLOPE2_Msk & ((value) << SFR_UTMIHSTRIM_SLOPE2_Pos)))
/* -------- SFR_UTMIFSTRIM : (SFR Offset: 0x38) UTMI Full Speed Trimming Register -------- */
#define SFR_UTMIFSTRIM_RISE_Pos 0
#define SFR_UTMIFSTRIM_RISE_Msk (0x7u << SFR_UTMIFSTRIM_RISE_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver Output Rising Slope Trimming */
#define SFR_UTMIFSTRIM_RISE(value) ((SFR_UTMIFSTRIM_RISE_Msk & ((value) << SFR_UTMIFSTRIM_RISE_Pos)))
#define SFR_UTMIFSTRIM_FALL_Pos 4
#define SFR_UTMIFSTRIM_FALL_Msk (0x7u << SFR_UTMIFSTRIM_FALL_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver Output Falling Slope Trimming */
#define SFR_UTMIFSTRIM_FALL(value) ((SFR_UTMIFSTRIM_FALL_Msk & ((value) << SFR_UTMIFSTRIM_FALL_Pos)))
#define SFR_UTMIFSTRIM_XCVR_Pos 8
#define SFR_UTMIFSTRIM_XCVR_Msk (0x3u << SFR_UTMIFSTRIM_XCVR_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver Crossover Voltage Trimming */
#define SFR_UTMIFSTRIM_XCVR(value) ((SFR_UTMIFSTRIM_XCVR_Msk & ((value) << SFR_UTMIFSTRIM_XCVR_Pos)))
#define SFR_UTMIFSTRIM_ZN_Pos 16
#define SFR_UTMIFSTRIM_ZN_Msk (0x7u << SFR_UTMIFSTRIM_ZN_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver NMOS Impedance Trimming */
#define SFR_UTMIFSTRIM_ZN(value) ((SFR_UTMIFSTRIM_ZN_Msk & ((value) << SFR_UTMIFSTRIM_ZN_Pos)))
#define SFR_UTMIFSTRIM_ZP_Pos 20
#define SFR_UTMIFSTRIM_ZP_Msk (0x7u << SFR_UTMIFSTRIM_ZP_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver PMOS Impedance Trimming */
#define SFR_UTMIFSTRIM_ZP(value) ((SFR_UTMIFSTRIM_ZP_Msk & ((value) << SFR_UTMIFSTRIM_ZP_Pos)))
/* -------- SFR_UTMISWAP : (SFR Offset: 0x3C) UTMI DP/DM Pin Swapping Register -------- */
#define SFR_UTMISWAP_PORT0 (0x1u << 0) /**< \brief (SFR_UTMISWAP) PORT 0 DP/DM Pin Swapping */
#define   SFR_UTMISWAP_PORT0_NORMAL (0x0u << 0) /**< \brief (SFR_UTMISWAP) DP/DM normal pinout. */
#define   SFR_UTMISWAP_PORT0_SWAPPED (0x1u << 0) /**< \brief (SFR_UTMISWAP) DP/DM swapped pinout. */
#define SFR_UTMISWAP_PORT1 (0x1u << 1) /**< \brief (SFR_UTMISWAP) PORT 1 DP/DM Pin Swapping */
#define   SFR_UTMISWAP_PORT1_NORMAL (0x0u << 1) /**< \brief (SFR_UTMISWAP) DP/DM normal pinout. */
#define   SFR_UTMISWAP_PORT1_SWAPPED (0x1u << 1) /**< \brief (SFR_UTMISWAP) DP/DM swapped pinout. */
#define SFR_UTMISWAP_PORT2 (0x1u << 2) /**< \brief (SFR_UTMISWAP) PORT 2 DP/DM Pin Swapping */
#define   SFR_UTMISWAP_PORT2_NORMAL (0x0u << 2) /**< \brief (SFR_UTMISWAP) DP/DM normal pinout. */
#define   SFR_UTMISWAP_PORT2_SWAPPED (0x1u << 2) /**< \brief (SFR_UTMISWAP) DP/DM swapped pinout. */
/* -------- SFR_EBICFG : (SFR Offset: 0x40) EBI Configuration Register -------- */
#define SFR_EBICFG_DRIVE0_Pos 0
#define SFR_EBICFG_DRIVE0_Msk (0x3u << SFR_EBICFG_DRIVE0_Pos) /**< \brief (SFR_EBICFG) EBI Pins Drive Level */
#define SFR_EBICFG_DRIVE0(value) ((SFR_EBICFG_DRIVE0_Msk & ((value) << SFR_EBICFG_DRIVE0_Pos)))
#define   SFR_EBICFG_DRIVE0_LOW (0x0u << 0) /**< \brief (SFR_EBICFG) Low drive level */
#define   SFR_EBICFG_DRIVE0_MEDIUM (0x2u << 0) /**< \brief (SFR_EBICFG) Medium drive level */
#define   SFR_EBICFG_DRIVE0_HIGH (0x3u << 0) /**< \brief (SFR_EBICFG) High drive level */
#define SFR_EBICFG_PULL0_Pos 2
#define SFR_EBICFG_PULL0_Msk (0x3u << SFR_EBICFG_PULL0_Pos) /**< \brief (SFR_EBICFG) EBI Pins Pull Value */
#define SFR_EBICFG_PULL0(value) ((SFR_EBICFG_PULL0_Msk & ((value) << SFR_EBICFG_PULL0_Pos)))
#define   SFR_EBICFG_PULL0_UP (0x0u << 2) /**< \brief (SFR_EBICFG) Pull-up */
#define   SFR_EBICFG_PULL0_NONE (0x1u << 2) /**< \brief (SFR_EBICFG) No Pull */
#define   SFR_EBICFG_PULL0_DOWN (0x3u << 2) /**< \brief (SFR_EBICFG) Pull-down */
#define SFR_EBICFG_SCH0 (0x1u << 4) /**< \brief (SFR_EBICFG) EBI Pins Schmitt Trigger */
#define SFR_EBICFG_DRIVE1_Pos 8
#define SFR_EBICFG_DRIVE1_Msk (0x3u << SFR_EBICFG_DRIVE1_Pos) /**< \brief (SFR_EBICFG) EBI Pins Drive Level */
#define SFR_EBICFG_DRIVE1(value) ((SFR_EBICFG_DRIVE1_Msk & ((value) << SFR_EBICFG_DRIVE1_Pos)))
#define   SFR_EBICFG_DRIVE1_LOW (0x0u << 8) /**< \brief (SFR_EBICFG) Low drive level */
#define   SFR_EBICFG_DRIVE1_MEDIUM (0x2u << 8) /**< \brief (SFR_EBICFG) Medium drive level */
#define   SFR_EBICFG_DRIVE1_HIGH (0x3u << 8) /**< \brief (SFR_EBICFG) High drive level */
#define SFR_EBICFG_PULL1_Pos 10
#define SFR_EBICFG_PULL1_Msk (0x3u << SFR_EBICFG_PULL1_Pos) /**< \brief (SFR_EBICFG) EBI Pins Pull Value */
#define SFR_EBICFG_PULL1(value) ((SFR_EBICFG_PULL1_Msk & ((value) << SFR_EBICFG_PULL1_Pos)))
#define   SFR_EBICFG_PULL1_UP (0x0u << 10) /**< \brief (SFR_EBICFG) Pull-up */
#define   SFR_EBICFG_PULL1_NONE (0x1u << 10) /**< \brief (SFR_EBICFG) No Pull */
#define   SFR_EBICFG_PULL1_DOWN (0x3u << 10) /**< \brief (SFR_EBICFG) Pull-down */
#define SFR_EBICFG_SCH1 (0x1u << 12) /**< \brief (SFR_EBICFG) EBI Pins Schmitt Trigger */
/* -------- SFR_CAN : (SFR Offset: 0x48) CAN Memories Address-based Register -------- */
#define SFR_CAN_EXT_MEM_CAN0_ADDR_Pos 0
#define SFR_CAN_EXT_MEM_CAN0_ADDR_Msk (0xffffu << SFR_CAN_EXT_MEM_CAN0_ADDR_Pos) /**< \brief (SFR_CAN) MSB CAN0 DMA Base Address */
#define SFR_CAN_EXT_MEM_CAN0_ADDR(value) ((SFR_CAN_EXT_MEM_CAN0_ADDR_Msk & ((value) << SFR_CAN_EXT_MEM_CAN0_ADDR_Pos)))
#define SFR_CAN_EXT_MEM_CAN1_ADDR_Pos 16
#define SFR_CAN_EXT_MEM_CAN1_ADDR_Msk (0xffffu << SFR_CAN_EXT_MEM_CAN1_ADDR_Pos) /**< \brief (SFR_CAN) MSB CAN1 DMA Base Address */
#define SFR_CAN_EXT_MEM_CAN1_ADDR(value) ((SFR_CAN_EXT_MEM_CAN1_ADDR_Msk & ((value) << SFR_CAN_EXT_MEM_CAN1_ADDR_Pos)))
/* -------- SFR_SN0 : (SFR Offset: 0x4C) Serial Number 0 Register -------- */
#define SFR_SN0_SN0_Pos 0
#define SFR_SN0_SN0_Msk (0xffffffffu << SFR_SN0_SN0_Pos) /**< \brief (SFR_SN0) Serial Number 0 */
/* -------- SFR_SN1 : (SFR Offset: 0x50) Serial Number 1 Register -------- */
#define SFR_SN1_SN1_Pos 0
#define SFR_SN1_SN1_Msk (0xffffffffu << SFR_SN1_SN1_Pos) /**< \brief (SFR_SN1) Serial Number 1 */
/* -------- SFR_AICREDIR : (SFR Offset: 0x54) AIC interrupt Redirection Register -------- */
#define SFR_AICREDIR_NSAIC (0x1u << 0) /**< \brief (SFR_AICREDIR) Interrupt redirection to Non-Secure AIC */
#define SFR_AICREDIR_AICREDIRKEY_Pos 1
#define SFR_AICREDIR_AICREDIRKEY_Msk (0x7fffffffu << SFR_AICREDIR_AICREDIRKEY_Pos) /**< \brief (SFR_AICREDIR) Unlock Key */
#define SFR_AICREDIR_AICREDIRKEY(value) ((SFR_AICREDIR_AICREDIRKEY_Msk & ((value) << SFR_AICREDIR_AICREDIRKEY_Pos)))
/* -------- SFR_L2CC_HRAMC : (SFR Offset: 0x58) L2CC_HRAMC1 -------- */
#define SFR_L2CC_HRAMC_SRAM_SEL (0x1u << 0) /**< \brief (SFR_L2CC_HRAMC) SRAM Selector */
/* -------- SFR_I2SCLKSEL : (SFR Offset: 0x90) I2SC Register -------- */
#define SFR_I2SCLKSEL_CLKSEL0 (0x1u << 0) /**< \brief (SFR_I2SCLKSEL) Clock Selection 0 */
#define SFR_I2SCLKSEL_CLKSEL1 (0x1u << 1) /**< \brief (SFR_I2SCLKSEL) Clock Selection 1 */
/* -------- QSPICLK_REG : (SFR Offset: 0x94) QSPI Clock Pad Supply Select Register -------- */
#define QSPICLK_REG_SUP_SEL (0x1u << 0) /**< \brief (QSPICLK_REG) Supply Selection */

/*@}*/


#endif /* _SAMA5D2_SFR_COMPONENT_ */
