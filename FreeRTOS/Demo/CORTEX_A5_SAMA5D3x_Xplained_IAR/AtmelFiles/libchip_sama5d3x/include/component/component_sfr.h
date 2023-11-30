/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following condition is met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _SAMA5_SFR_COMPONENT_
#define _SAMA5_SFR_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Special Function Registers */
/* ============================================================================= */
/** \addtogroup SAMA5_SFR Special Function Registers */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Sfr hardware registers */
typedef struct {
  RoReg Reserved1[4];
  RwReg SFR_OHCIICR;    /**< \brief (Sfr Offset: 0x10) OHCI Interrupt Configuration Register */
  RoReg SFR_OHCIISR;    /**< \brief (Sfr Offset: 0x14) OHCI Interrupt Status Register */
  RoReg Reserved2[2];
  RwReg SFR_AHB;        /**< \brief (Sfr Offset: 0x20) AHB Configuration Register */
  RwReg SFR_BRIDGE;     /**< \brief (Sfr Offset: 0x24) Bridge Configuration Register */
  RwReg SFR_SECURE;     /**< \brief (Sfr Offset: 0x28) Security Configuration Register */
  RoReg Reserved3[1];
  RwReg SFR_UTMICKTRIM; /**< \brief (Sfr Offset: 0x30) UTMI Clock Trimming Register */
  RwReg SFR_UTMIHSTRIM; /**< \brief (Sfr Offset: 0x34) UTMI High Speed Trimming Register */
  RwReg SFR_UTMIFSTRIM; /**< \brief (Sfr Offset: 0x38) UTMI Full Speed Trimming Register */
  RwReg SFR_UTMISWAP;   /**< \brief (Sfr Offset: 0x3C) UTMI DP/DM Pin Swapping Register */
  RwReg SFR_EBICFG;     /**< \brief (Sfr Offset: 0x40) EBI Configuration Register */
} Sfr;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SFR_OHCIICR : (SFR Offset: 0x10) OHCI Interrupt Configuration Register -------- */
#define SFR_OHCIICR_RES0 (0x1u << 0) /**< \brief (SFR_OHCIICR) USB PORTx RESET */
#define SFR_OHCIICR_RES1 (0x1u << 1) /**< \brief (SFR_OHCIICR) USB PORTx RESET */
#define SFR_OHCIICR_RES2 (0x1u << 2) /**< \brief (SFR_OHCIICR) USB PORTx RESET */
#define SFR_OHCIICR_ARIE (0x1u << 4) /**< \brief (SFR_OHCIICR) OHCI Asynchronous Resume Interrupt Enable */
#define SFR_OHCIICR_APPSTART (0x1u << 5) /**< \brief (SFR_OHCIICR) Reserved */
#define SFR_OHCIICR_UDPPUDIS (0x1u << 23) /**< \brief (SFR_OHCIICR) OHCI USB DEVICE PULL-UP DISABLE */
/* -------- SFR_OHCIISR : (SFR Offset: 0x14) OHCI Interrupt Status Register -------- */
#define SFR_OHCIISR_RIS0 (0x1u << 0) /**< \brief (SFR_OHCIISR) OHCI Resume Interrupt Status Port 0 */
#define SFR_OHCIISR_RIS1 (0x1u << 1) /**< \brief (SFR_OHCIISR) OHCI Resume Interrupt Status Port 1 */
#define SFR_OHCIISR_RIS2 (0x1u << 2) /**< \brief (SFR_OHCIISR) OHCI Resume Interrupt Status Port 2 */
/* -------- SFR_AHB : (SFR Offset: 0x20) AHB Configuration Register -------- */
#define SFR_AHB_PFETCH10 (0x1u << 10) /**< \brief (SFR_AHB) AHB MASTERx 10 Converter Prefetch */
#define   SFR_AHB_PFETCH10_INCR4 (0x0u << 10) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 4 beats. */
#define   SFR_AHB_PFETCH10_INCR8 (0x1u << 10) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 8 beats. */
#define SFR_AHB_PFETCH11 (0x1u << 11) /**< \brief (SFR_AHB) AHB MASTERx 11 Converter Prefetch */
#define   SFR_AHB_PFETCH11_INCR4 (0x0u << 11) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 4 beats. */
#define   SFR_AHB_PFETCH11_INCR8 (0x1u << 11) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 8 beats. */
#define SFR_AHB_PFETCH12 (0x1u << 12) /**< \brief (SFR_AHB) AHB MASTERx 12 Converter Prefetch */
#define   SFR_AHB_PFETCH12_INCR4 (0x0u << 12) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 4 beats. */
#define   SFR_AHB_PFETCH12_INCR8 (0x1u << 12) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 8 beats. */
#define SFR_AHB_PFETCH13 (0x1u << 13) /**< \brief (SFR_AHB) AHB MASTERx 13 Converter Prefetch */
#define   SFR_AHB_PFETCH13_INCR4 (0x0u << 13) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 4 beats. */
#define   SFR_AHB_PFETCH13_INCR8 (0x1u << 13) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 8 beats. */
#define SFR_AHB_PFETCH14 (0x1u << 14) /**< \brief (SFR_AHB) AHB MASTERx 14 Converter Prefetch */
#define   SFR_AHB_PFETCH14_INCR4 (0x0u << 14) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 4 beats. */
#define   SFR_AHB_PFETCH14_INCR8 (0x1u << 14) /**< \brief (SFR_AHB) INCR undefined burst converted to burst of 8 beats. */
#define SFR_AHB_DLBOPT10 (0x1u << 26) /**< \brief (SFR_AHB) AHB MASTERx 10 Converter Define Length Burst Optimization */
#define SFR_AHB_DLBOPT11 (0x1u << 27) /**< \brief (SFR_AHB) AHB MASTERx 11 Converter Define Length Burst Optimization */
#define SFR_AHB_DLBOPT12 (0x1u << 28) /**< \brief (SFR_AHB) AHB MASTERx 12 Converter Define Length Burst Optimization */
#define SFR_AHB_DLBOPT13 (0x1u << 29) /**< \brief (SFR_AHB) AHB MASTERx 13 Converter Define Length Burst Optimization */
#define SFR_AHB_DLBOPT14 (0x1u << 30) /**< \brief (SFR_AHB) AHB MASTERx 14 Converter Define Length Burst Optimization */
/* -------- SFR_BRIDGE : (SFR Offset: 0x24) Bridge Configuration Register -------- */
#define SFR_BRIDGE_APBTURBO (0x1u << 0) /**< \brief (SFR_BRIDGE) AHB to APB Bridge mode */
#define SFR_BRIDGE_AXI2AHBSEL (0x1u << 8) /**< \brief (SFR_BRIDGE) AXI to AHB bridge for DDR controller selection */
#define   SFR_BRIDGE_AXI2AHBSEL_SINGLE (0x0u << 8) /**< \brief (SFR_BRIDGE) use single port bridge. */
#define   SFR_BRIDGE_AXI2AHBSEL_DUAL (0x1u << 8) /**< \brief (SFR_BRIDGE) use dual port bridge. */
/* -------- SFR_SECURE : (SFR Offset: 0x28) Security Configuration Register -------- */
#define SFR_SECURE_ROM (0x1u << 0) /**< \brief (SFR_SECURE) Disable Access to ROM Code */
#define SFR_SECURE_FUSE (0x1u << 8) /**< \brief (SFR_SECURE) Disable Access to Fuse Controller */
/* -------- SFR_UTMICKTRIM : (SFR Offset: 0x30) UTMI Clock Trimming Register -------- */
#define SFR_UTMICKTRIM_FREQ_Pos 0
#define SFR_UTMICKTRIM_FREQ_Msk (0x3u << SFR_UTMICKTRIM_FREQ_Pos) /**< \brief (SFR_UTMICKTRIM) UTMI Reference Clock Frequency */
#define   SFR_UTMICKTRIM_FREQ_12 (0x0u << 0) /**< \brief (SFR_UTMICKTRIM) 12 MHz reference clock */
#define   SFR_UTMICKTRIM_FREQ_16 (0x1u << 0) /**< \brief (SFR_UTMICKTRIM) 16 MHz reference clock */
#define   SFR_UTMICKTRIM_FREQ_24 (0x2u << 0) /**< \brief (SFR_UTMICKTRIM) 24 MHz reference clock */
#define   SFR_UTMICKTRIM_FREQ_48 (0x3u << 0) /**< \brief (SFR_UTMICKTRIM) 48 MHz reference clock */
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
#define SFR_UTMIFSTRIM_RISE_Msk (0x7u << SFR_UTMIFSTRIM_RISE_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver output rising slope trimming */
#define SFR_UTMIFSTRIM_RISE(value) ((SFR_UTMIFSTRIM_RISE_Msk & ((value) << SFR_UTMIFSTRIM_RISE_Pos)))
#define SFR_UTMIFSTRIM_FALL_Pos 4
#define SFR_UTMIFSTRIM_FALL_Msk (0x7u << SFR_UTMIFSTRIM_FALL_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver output falling slope trimming */
#define SFR_UTMIFSTRIM_FALL(value) ((SFR_UTMIFSTRIM_FALL_Msk & ((value) << SFR_UTMIFSTRIM_FALL_Pos)))
#define SFR_UTMIFSTRIM_XCVR_Pos 8
#define SFR_UTMIFSTRIM_XCVR_Msk (0x3u << SFR_UTMIFSTRIM_XCVR_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver crossover voltage trimming */
#define SFR_UTMIFSTRIM_XCVR(value) ((SFR_UTMIFSTRIM_XCVR_Msk & ((value) << SFR_UTMIFSTRIM_XCVR_Pos)))
#define SFR_UTMIFSTRIM_ZN_Pos 16
#define SFR_UTMIFSTRIM_ZN_Msk (0x7u << SFR_UTMIFSTRIM_ZN_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver NMOS impedance trimming */
#define SFR_UTMIFSTRIM_ZN(value) ((SFR_UTMIFSTRIM_ZN_Msk & ((value) << SFR_UTMIFSTRIM_ZN_Pos)))
#define SFR_UTMIFSTRIM_ZP_Pos 20
#define SFR_UTMIFSTRIM_ZP_Msk (0x7u << SFR_UTMIFSTRIM_ZP_Pos) /**< \brief (SFR_UTMIFSTRIM) FS Transceiver PMOS impedance trimming */
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
#define   SFR_EBICFG_DRIVE0_LOW (0x0u << 0) /**< \brief (SFR_EBICFG) Low drive level */
#define   SFR_EBICFG_DRIVE0_MEDIUM (0x2u << 0) /**< \brief (SFR_EBICFG) Medium drive level */
#define   SFR_EBICFG_DRIVE0_HIGH (0x3u << 0) /**< \brief (SFR_EBICFG) High drive level */
#define SFR_EBICFG_PULL0_Pos 2
#define SFR_EBICFG_PULL0_Msk (0x3u << SFR_EBICFG_PULL0_Pos) /**< \brief (SFR_EBICFG) EBI Pins Pull Value */
#define   SFR_EBICFG_PULL0_UP (0x0u << 2) /**< \brief (SFR_EBICFG) Pull-up */
#define   SFR_EBICFG_PULL0_NONE (0x1u << 2) /**< \brief (SFR_EBICFG) No Pull */
#define   SFR_EBICFG_PULL0_DOWN (0x3u << 2) /**< \brief (SFR_EBICFG) Pull-down */
#define SFR_EBICFG_SCH0 (0x1u << 4) /**< \brief (SFR_EBICFG) EBI Pins Schmitt Trigger */
#define SFR_EBICFG_DRIVE1_Pos 8
#define SFR_EBICFG_DRIVE1_Msk (0x3u << SFR_EBICFG_DRIVE1_Pos) /**< \brief (SFR_EBICFG) EBI Pins Drive Level */
#define   SFR_EBICFG_DRIVE1_LOW (0x0u << 8) /**< \brief (SFR_EBICFG) Low drive level */
#define   SFR_EBICFG_DRIVE1_MEDIUM (0x2u << 8) /**< \brief (SFR_EBICFG) Medium drive level */
#define   SFR_EBICFG_DRIVE1_HIGH (0x3u << 8) /**< \brief (SFR_EBICFG) High drive level */
#define SFR_EBICFG_PULL1_Pos 10
#define SFR_EBICFG_PULL1_Msk (0x3u << SFR_EBICFG_PULL1_Pos) /**< \brief (SFR_EBICFG) EBI Pins Pull Value */
#define   SFR_EBICFG_PULL1_UP (0x0u << 10) /**< \brief (SFR_EBICFG) Pull-up */
#define   SFR_EBICFG_PULL1_NONE (0x1u << 10) /**< \brief (SFR_EBICFG) No Pull */
#define   SFR_EBICFG_PULL1_DOWN (0x3u << 10) /**< \brief (SFR_EBICFG) Pull-down */
#define SFR_EBICFG_SCH1 (0x1u << 12) /**< \brief (SFR_EBICFG) EBI Pins Schmitt Trigger */
#define SFR_EBICFG_BMS (0x1u << 16) /**< \brief (SFR_EBICFG) BMS Sampled Value (Read Only) */
#define   SFR_EBICFG_BMS_ROM (0x0u << 16) /**< \brief (SFR_EBICFG) Boot on ROM. */
#define   SFR_EBICFG_BMS_EBI (0x1u << 16) /**< \brief (SFR_EBICFG) Boot on EBI. */

/*@}*/


#endif /* _SAMA5_SFR_COMPONENT_ */
