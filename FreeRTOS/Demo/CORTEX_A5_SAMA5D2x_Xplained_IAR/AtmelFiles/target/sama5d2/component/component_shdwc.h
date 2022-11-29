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

#ifndef _SAMA5D2_SHDWC_COMPONENT_
#define _SAMA5D2_SHDWC_COMPONENT_

/* ============================================================================= */
/**  SOFTWARE API DEFINITION FOR Shutdown Controller */
/* ============================================================================= */
/** \addtogroup SAMA5D2_SHDWC Shutdown Controller */
/*@{*/

#if !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__))
/** \brief Shdwc hardware registers */
typedef struct {
  __O  uint32_t SHDW_CR;   /**< \brief (Shdwc Offset: 0x00) Shutdown Control Register */
  __IO uint32_t SHDW_MR;   /**< \brief (Shdwc Offset: 0x04) Shutdown Mode Register */
  __I  uint32_t SHDW_SR;   /**< \brief (Shdwc Offset: 0x08) Shutdown Status Register */
  __IO uint32_t SHDW_WUIR; /**< \brief (Shdwc Offset: 0x0C) Shutdown Wake-up Inputs Register */
} Shdwc;
#endif /* !(defined(__ASSEMBLY__) || defined(__IAR_SYSTEMS_ASM__)) */
/* -------- SHDW_CR : (SHDWC Offset: 0x00) Shutdown Control Register -------- */
#define SHDW_CR_SHDW (0x1u << 0) /**< \brief (SHDW_CR) Shutdown Command */
#define SHDW_CR_KEY_Pos 24
#define SHDW_CR_KEY_Msk (0xffu << SHDW_CR_KEY_Pos) /**< \brief (SHDW_CR) Password */
#define SHDW_CR_KEY(value) ((SHDW_CR_KEY_Msk & ((value) << SHDW_CR_KEY_Pos)))
#define   SHDW_CR_KEY_PASSWD (0xA5u << 24) /**< \brief (SHDW_CR) Writing any other value in this field aborts the write operation. */
/* -------- SHDW_MR : (SHDWC Offset: 0x04) Shutdown Mode Register -------- */
#define SHDW_MR_LPDBCEN0 (0x1u << 0) /**< \brief (SHDW_MR) Low-Power Debouncer Enable WKUP0 */
#define   SHDW_MR_LPDBCEN0_NOT_ENABLE (0x0u << 0) /**< \brief (SHDW_MR) The WKUP0 input pin is not connected to the low-power debouncer. */
#define   SHDW_MR_LPDBCEN0_ENABLE (0x1u << 0) /**< \brief (SHDW_MR) The WKUP0 input pin is connected to the low-power debouncer and can force a system wake-up. */
#define SHDW_MR_LPDBCEN1 (0x1u << 1) /**< \brief (SHDW_MR) Low-Power Debouncer Enable WKUP1 */
#define   SHDW_MR_LPDBCEN1_NOT_ENABLE (0x0u << 1) /**< \brief (SHDW_MR) The WKUP1 input pin is not connected to the low-power debouncer. */
#define   SHDW_MR_LPDBCEN1_ENABLE (0x1u << 1) /**< \brief (SHDW_MR) The WKUP1 input pin is connected to the low-power debouncer and can force a system wake-up. */
#define SHDW_MR_LPDBC_Pos 8
#define SHDW_MR_LPDBC_Msk (0x7u << SHDW_MR_LPDBC_Pos) /**< \brief (SHDW_MR) Low Power Debouncer Period */
#define SHDW_MR_LPDBC(value) ((SHDW_MR_LPDBC_Msk & ((value) << SHDW_MR_LPDBC_Pos)))
#define   SHDW_MR_LPDBC_DISABLE (0x0u << 8) /**< \brief (SHDW_MR) Disable the low-power debouncers */
#define   SHDW_MR_LPDBC_2_RTCOUT0 (0x1u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 2 RTCOUT0 periods */
#define   SHDW_MR_LPDBC_3_RTCOUT0 (0x2u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 3 RTCOUT0 periods */
#define   SHDW_MR_LPDBC_4_RTCOUT0 (0x3u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 4 RTCOUT0 periods */
#define   SHDW_MR_LPDBC_5_RTCOUT0 (0x4u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 5 RTCOUT0 periods */
#define   SHDW_MR_LPDBC_6_RTCOUT0 (0x5u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 6 RTCOUT0 periods */
#define   SHDW_MR_LPDBC_7_RTCOUT0 (0x6u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 7 RTCOUT0 periods */
#define   SHDW_MR_LPDBC_8_RTCOUT0 (0x7u << 8) /**< \brief (SHDW_MR) WKUP0/1 in active state for at least 8 RTCOUT0 periods */
#define SHDW_MR_RTTWKEN (0x1u << 16) /**< \brief (SHDW_MR)  */
#define SHDW_MR_RTCWKEN (0x1u << 17) /**< \brief (SHDW_MR) Analog Comparator Controller Wake-up Enable */
#define SHDW_MR_ACCWKEN (0x1u << 18) /**< \brief (SHDW_MR) Analog Comparator Controller Wake-up Enable */
#define SHDW_MR_RXLPWKEN (0x1u << 19) /**< \brief (SHDW_MR) Debug Unit Wake-up Enable */
#define SHDW_MR_WKUPDBC_Pos 24
#define SHDW_MR_WKUPDBC_Msk (0x7u << SHDW_MR_WKUPDBC_Pos) /**< \brief (SHDW_MR) Wake-up Inputs Debouncer Period */
#define SHDW_MR_WKUPDBC(value) ((SHDW_MR_WKUPDBC_Msk & ((value) << SHDW_MR_WKUPDBC_Pos)))
#define   SHDW_MR_WKUPDBC_IMMEDIATE (0x0u << 24) /**< \brief (SHDW_MR) Immediate, no debouncing, detected active at least on one Slow Clock edge */
#define   SHDW_MR_WKUPDBC_3_SLCK (0x1u << 24) /**< \brief (SHDW_MR) WKUPx shall be in its active state for at least 3 SLCK periods */
#define   SHDW_MR_WKUPDBC_32_SLCK (0x2u << 24) /**< \brief (SHDW_MR) WKUPx shall be in its active state for at least 32 SLCK periods */
#define   SHDW_MR_WKUPDBC_512_SLCK (0x3u << 24) /**< \brief (SHDW_MR) WKUPx shall be in its active state for at least 512 SLCK periods */
#define   SHDW_MR_WKUPDBC_4096_SLCK (0x4u << 24) /**< \brief (SHDW_MR) WKUPx shall be in its active state for at least 4,096 SLCK periods */
#define   SHDW_MR_WKUPDBC_32768_SLCK (0x5u << 24) /**< \brief (SHDW_MR) WKUPx shall be in its active state for at least 32,768 SLCK periods */
/* -------- SHDW_SR : (SHDWC Offset: 0x08) Shutdown Status Register -------- */
#define SHDW_SR_WKUPS (0x1u << 0) /**< \brief (SHDW_SR) WKUP Wake-up Status */
#define   SHDW_SR_WKUPS_NO (0x0u << 0) /**< \brief (SHDW_SR) No wake-up due to the assertion of the WKUP pins has occurred since the last read of SUPC_SR. */
#define   SHDW_SR_WKUPS_PRESENT (0x1u << 0) /**< \brief (SHDW_SR) At least one wake-up due to the assertion of the WKUP pins has occurred since the last read of SUPC_SR. */
#define SHDW_SR_ACCWK (0x1u << 6) /**< \brief (SHDW_SR) Analog Comparator Controller Wake-up */
#define SHDW_SR_RXLPWK (0x1u << 7) /**< \brief (SHDW_SR) Debug Unit Wake-up */
#define SHDW_SR_WKUPIS0 (0x1u << 16) /**< \brief (SHDW_SR) Wake-up 0 Input Status */
#define   SHDW_SR_WKUPIS0_DISABLE (0x0u << 16) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS0_ENABLE (0x1u << 16) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS1 (0x1u << 17) /**< \brief (SHDW_SR) Wake-up 1 Input Status */
#define   SHDW_SR_WKUPIS1_DISABLE (0x0u << 17) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS1_ENABLE (0x1u << 17) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS2 (0x1u << 18) /**< \brief (SHDW_SR) Wake-up 2 Input Status */
#define   SHDW_SR_WKUPIS2_DISABLE (0x0u << 18) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS2_ENABLE (0x1u << 18) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS3 (0x1u << 19) /**< \brief (SHDW_SR) Wake-up 3 Input Status */
#define   SHDW_SR_WKUPIS3_DISABLE (0x0u << 19) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS3_ENABLE (0x1u << 19) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS4 (0x1u << 20) /**< \brief (SHDW_SR) Wake-up 4 Input Status */
#define   SHDW_SR_WKUPIS4_DISABLE (0x0u << 20) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS4_ENABLE (0x1u << 20) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS5 (0x1u << 21) /**< \brief (SHDW_SR) Wake-up 5 Input Status */
#define   SHDW_SR_WKUPIS5_DISABLE (0x0u << 21) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS5_ENABLE (0x1u << 21) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS6 (0x1u << 22) /**< \brief (SHDW_SR) Wake-up 6 Input Status */
#define   SHDW_SR_WKUPIS6_DISABLE (0x0u << 22) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS6_ENABLE (0x1u << 22) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS7 (0x1u << 23) /**< \brief (SHDW_SR) Wake-up 7 Input Status */
#define   SHDW_SR_WKUPIS7_DISABLE (0x0u << 23) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS7_ENABLE (0x1u << 23) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
#define SHDW_SR_WKUPIS8 (0x1u << 24) /**< \brief (SHDW_SR) Wake-up 8 Input Status */
#define   SHDW_SR_WKUPIS8_DISABLE (0x0u << 24) /**< \brief (SHDW_SR) The corresponding wake-up input is disabled, or was inactive at the time the debouncer triggered a wake-up event. */
#define   SHDW_SR_WKUPIS8_ENABLE (0x1u << 24) /**< \brief (SHDW_SR) The corresponding wake-up input was active at the time the debouncer triggered a wake-up event. */
/* -------- SHDW_WUIR : (SHDWC Offset: 0x0C) Shutdown Wake-up Inputs Register -------- */
#define SHDW_WUIR_WKUPEN0 (0x1u << 0) /**< \brief (SHDW_WUIR) Wake-up 0 Input Enable */
#define   SHDW_WUIR_WKUPEN0_DISABLE (0x0u << 0) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN0_ENABLE (0x1u << 0) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN1 (0x1u << 1) /**< \brief (SHDW_WUIR) Wake-up 1 Input Enable */
#define   SHDW_WUIR_WKUPEN1_DISABLE (0x0u << 1) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN1_ENABLE (0x1u << 1) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN2 (0x1u << 2) /**< \brief (SHDW_WUIR) Wake-up 2 Input Enable */
#define   SHDW_WUIR_WKUPEN2_DISABLE (0x0u << 2) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN2_ENABLE (0x1u << 2) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN3 (0x1u << 3) /**< \brief (SHDW_WUIR) Wake-up 3 Input Enable */
#define   SHDW_WUIR_WKUPEN3_DISABLE (0x0u << 3) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN3_ENABLE (0x1u << 3) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN4 (0x1u << 4) /**< \brief (SHDW_WUIR) Wake-up 4 Input Enable */
#define   SHDW_WUIR_WKUPEN4_DISABLE (0x0u << 4) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN4_ENABLE (0x1u << 4) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN5 (0x1u << 5) /**< \brief (SHDW_WUIR) Wake-up 5 Input Enable */
#define   SHDW_WUIR_WKUPEN5_DISABLE (0x0u << 5) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN5_ENABLE (0x1u << 5) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN6 (0x1u << 6) /**< \brief (SHDW_WUIR) Wake-up 6 Input Enable */
#define   SHDW_WUIR_WKUPEN6_DISABLE (0x0u << 6) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN6_ENABLE (0x1u << 6) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN7 (0x1u << 7) /**< \brief (SHDW_WUIR) Wake-up 7 Input Enable */
#define   SHDW_WUIR_WKUPEN7_DISABLE (0x0u << 7) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN7_ENABLE (0x1u << 7) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPEN8 (0x1u << 8) /**< \brief (SHDW_WUIR) Wake-up 8 Input Enable */
#define   SHDW_WUIR_WKUPEN8_DISABLE (0x0u << 8) /**< \brief (SHDW_WUIR) The corresponding wake-up input has no wake-up effect. */
#define   SHDW_WUIR_WKUPEN8_ENABLE (0x1u << 8) /**< \brief (SHDW_WUIR) The corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT0 (0x1u << 16) /**< \brief (SHDW_WUIR) Wake-up 0 Input Type */
#define   SHDW_WUIR_WKUPT0_LOW (0x0u << 16) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT0_HIGH (0x1u << 16) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT1 (0x1u << 17) /**< \brief (SHDW_WUIR) Wake-up 1 Input Type */
#define   SHDW_WUIR_WKUPT1_LOW (0x0u << 17) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT1_HIGH (0x1u << 17) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT2 (0x1u << 18) /**< \brief (SHDW_WUIR) Wake-up 2 Input Type */
#define   SHDW_WUIR_WKUPT2_LOW (0x0u << 18) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT2_HIGH (0x1u << 18) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT3 (0x1u << 19) /**< \brief (SHDW_WUIR) Wake-up 3 Input Type */
#define   SHDW_WUIR_WKUPT3_LOW (0x0u << 19) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT3_HIGH (0x1u << 19) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT4 (0x1u << 20) /**< \brief (SHDW_WUIR) Wake-up 4 Input Type */
#define   SHDW_WUIR_WKUPT4_LOW (0x0u << 20) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT4_HIGH (0x1u << 20) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT5 (0x1u << 21) /**< \brief (SHDW_WUIR) Wake-up 5 Input Type */
#define   SHDW_WUIR_WKUPT5_LOW (0x0u << 21) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT5_HIGH (0x1u << 21) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT6 (0x1u << 22) /**< \brief (SHDW_WUIR) Wake-up 6 Input Type */
#define   SHDW_WUIR_WKUPT6_LOW (0x0u << 22) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT6_HIGH (0x1u << 22) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT7 (0x1u << 23) /**< \brief (SHDW_WUIR) Wake-up 7 Input Type */
#define   SHDW_WUIR_WKUPT7_LOW (0x0u << 23) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT7_HIGH (0x1u << 23) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define SHDW_WUIR_WKUPT8 (0x1u << 24) /**< \brief (SHDW_WUIR) Wake-up 8 Input Type */
#define   SHDW_WUIR_WKUPT8_LOW (0x0u << 24) /**< \brief (SHDW_WUIR) A falling edge followed by a low level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */
#define   SHDW_WUIR_WKUPT8_HIGH (0x1u << 24) /**< \brief (SHDW_WUIR) A rising edge followed by a high level, for a period defined by WKUPDBC, on the corresponding wake-up input forces the wake-up of the core power supply. */

/*@}*/


#endif /* _SAMA5D2_SHDWC_COMPONENT_ */
