/** @file pinmux.h
 *   @brief PINMUX Driver Implementation File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __PINMUX_H__
#define __PINMUX_H__

#include "reg_pinmux.h"

#ifdef __cplusplus
extern "C" {
#endif

#define PINMUX_BALL_A4_SHIFT              0U
#define PINMUX_BALL_A5_SHIFT              8U
#define PINMUX_BALL_A11_SHIFT             8U
#define PINMUX_BALL_A14_SHIFT             0U
#define PINMUX_BALL_B2_SHIFT              24U
#define PINMUX_BALL_B3_SHIFT              8U
#define PINMUX_BALL_B4_SHIFT              16U
#define PINMUX_BALL_B5_SHIFT              24U
#define PINMUX_BALL_B11_SHIFT             8U
#define PINMUX_BALL_B12_SHIFT             0U
#define PINMUX_BALL_C1_SHIFT              0U
#define PINMUX_BALL_C2_SHIFT              0U
#define PINMUX_BALL_C3_SHIFT              16U
#define PINMUX_BALL_C4_SHIFT              16U
#define PINMUX_BALL_C5_SHIFT              8U
#define PINMUX_BALL_C6_SHIFT              0U
#define PINMUX_BALL_D3_SHIFT              0U
#define PINMUX_BALL_D4_SHIFT              0U
#define PINMUX_BALL_D5_SHIFT              0U
#define PINMUX_BALL_D16_SHIFT             24U
#define PINMUX_BALL_D17_SHIFT             16U
#define PINMUX_BALL_D19_SHIFT             0U
#define PINMUX_BALL_E1_SHIFT              16U
#define PINMUX_BALL_E3_SHIFT              8U
#define PINMUX_BALL_E18_SHIFT             0U
#define PINMUX_BALL_E19_SHIFT             0U
#define PINMUX_BALL_F3_SHIFT              16U
#define PINMUX_BALL_G3_SHIFT              8U
#define PINMUX_BALL_G19_SHIFT             16U
#define PINMUX_BALL_H3_SHIFT              16U
#define PINMUX_BALL_H18_SHIFT             24U
#define PINMUX_BALL_H19_SHIFT             16U
#define PINMUX_BALL_J1_SHIFT              8U
#define PINMUX_BALL_J3_SHIFT              24U
#define PINMUX_BALL_J18_SHIFT             0U
#define PINMUX_BALL_J19_SHIFT             8U
#define PINMUX_BALL_K2_SHIFT              8U
#define PINMUX_BALL_K17_SHIFT             0U
#define PINMUX_BALL_K18_SHIFT             0U
#define PINMUX_BALL_K19_SHIFT             8U
#define PINMUX_BALL_M1_SHIFT              0U
#define PINMUX_BALL_M2_SHIFT              24U
#define PINMUX_BALL_N1_SHIFT              16U
#define PINMUX_BALL_N2_SHIFT              0U
#define PINMUX_BALL_N17_SHIFT             16U
#define PINMUX_BALL_N19_SHIFT             0U
#define PINMUX_BALL_P1_SHIFT              24U
#define PINMUX_BALL_P2_SHIFT              16U
#define PINMUX_BALL_R2_SHIFT              24U
#define PINMUX_BALL_T1_SHIFT              0U
#define PINMUX_BALL_U1_SHIFT              24U
#define PINMUX_BALL_V2_SHIFT              16U
#define PINMUX_BALL_V5_SHIFT              8U
#define PINMUX_BALL_V6_SHIFT              16U
#define PINMUX_BALL_V7_SHIFT              16U
#define PINMUX_BALL_V8_SHIFT              8U
#define PINMUX_BALL_V9_SHIFT              24U
#define PINMUX_BALL_V10_SHIFT             16U
#define PINMUX_BALL_W3_SHIFT              16U
#define PINMUX_BALL_W5_SHIFT              8U
#define PINMUX_BALL_W8_SHIFT              16U
#define PINMUX_BALL_W9_SHIFT              8U
#define PINMUX_BALL_W10_SHIFT             0U

#define PINMUX_GATE_EMIF_CLK_SHIFT        8U
#define PINMUX_GIOB_DISABLE_HET2_SHIFT    16U
#define PINMUX_ALT_ADC_TRIGGER_SHIFT      0U
#define PINMUX_ETHERNET_SHIFT             24U
#define PINMUX_ETPWM1_SHIFT               0U
#define PINMUX_ETPWM2_SHIFT               8U
#define PINMUX_ETPWM3_SHIFT               16U
#define PINMUX_ETPWM4_SHIFT               24U
#define PINMUX_ETPWM5_SHIFT               0U
#define PINMUX_ETPWM6_SHIFT               8U
#define PINMUX_ETPWM7_SHIFT               16U
#define PINMUX_ETPWM_TIME_BASE_SYNC_SHIFT 24U
#define PINMUX_ETPWM_TBCLK_SYNC_SHIFT     0U
#define PINMUX_TZ1_SHIFT                  16U
#define PINMUX_TZ2_SHIFT                  24U
#define PINMUX_TZ3_SHIFT                  0U
#define PINMUX_EPWM1SYNCI_SHIFT           8U

#define PINMUX_BALL_A4_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A4_SHIFT ) )
#define PINMUX_BALL_A5_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A5_SHIFT ) )
#define PINMUX_BALL_A11_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A11_SHIFT ) )
#define PINMUX_BALL_A14_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A14_SHIFT ) )
#define PINMUX_BALL_B2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B3_SHIFT ) )
#define PINMUX_BALL_B4_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_B5_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B5_SHIFT ) )
#define PINMUX_BALL_B11_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_B12_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B12_SHIFT ) )
#define PINMUX_BALL_C1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C2_SHIFT ) )
#define PINMUX_BALL_C3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C4_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C4_SHIFT ) )
#define PINMUX_BALL_C5_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C5_SHIFT ) )
#define PINMUX_BALL_C6_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C6_SHIFT ) )
#define PINMUX_BALL_D3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D3_SHIFT ) )
#define PINMUX_BALL_D4_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D4_SHIFT ) )
#define PINMUX_BALL_D5_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D5_SHIFT ) )
#define PINMUX_BALL_D16_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D16_SHIFT ) )
#define PINMUX_BALL_D17_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D17_SHIFT ) )
#define PINMUX_BALL_D19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_E1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E1_SHIFT ) )
#define PINMUX_BALL_E3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E18_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_E19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E19_SHIFT ) )
#define PINMUX_BALL_F3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_G3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G3_SHIFT ) )
#define PINMUX_BALL_G19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_H3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H3_SHIFT ) )
#define PINMUX_BALL_H18_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_J1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J1_SHIFT ) )
#define PINMUX_BALL_J3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J3_SHIFT ) )
#define PINMUX_BALL_J18_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_J19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_K2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K2_SHIFT ) )
#define PINMUX_BALL_K17_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K17_SHIFT ) )
#define PINMUX_BALL_K18_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K18_SHIFT ) )
#define PINMUX_BALL_K19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_M1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_M1_SHIFT ) )
#define PINMUX_BALL_M2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_M2_SHIFT ) )
#define PINMUX_BALL_N1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_N2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N17_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N17_SHIFT ) )
#define PINMUX_BALL_N19_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_P1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P2_SHIFT ) )
#define PINMUX_BALL_R2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_T1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T12_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_T12_SHIFT ) )
#define PINMUX_BALL_U1_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_V2_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V5_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V5_SHIFT ) )
#define PINMUX_BALL_V6_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V7_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V8_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V8_SHIFT ) )
#define PINMUX_BALL_V9_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V9_SHIFT ) )
#define PINMUX_BALL_V10_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_W3_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W3_SHIFT ) )
#define PINMUX_BALL_W5_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W5_SHIFT ) )
#define PINMUX_BALL_W8_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W8_SHIFT ) )
#define PINMUX_BALL_W9_MASK               ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W10_MASK              ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W10_SHIFT ) )

#define PINMUX_GATE_EMIF_CLK_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GATE_EMIF_CLK_SHIFT ) )
#define PINMUX_GIOB_DISABLE_HET2_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB_DISABLE_HET2_SHIFT ) )
#define PINMUX_ALT_ADC_TRIGGER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ALT_ADC_TRIGGER_SHIFT ) )
#define PINMUX_ETHERNET_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETHERNET_SHIFT ) )

#define PINMUX_ETPWM1_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM1_SHIFT ) )
#define PINMUX_ETPWM2_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM2_SHIFT ) )
#define PINMUX_ETPWM3_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM3_SHIFT ) )
#define PINMUX_ETPWM4_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM4_SHIFT ) )
#define PINMUX_ETPWM5_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM5_SHIFT ) )
#define PINMUX_ETPWM6_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM6_SHIFT ) )
#define PINMUX_ETPWM7_MASK   ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM7_SHIFT ) )
#define PINMUX_ETPWM_TIME_BASE_SYNC_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_TIME_BASE_SYNC_SHIFT ) )
#define PINMUX_ETPWM_TBCLK_SYNC_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_TBCLK_SYNC_SHIFT ) )
#define PINMUX_TZ1_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_TZ1_SHIFT ) )
#define PINMUX_TZ2_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_TZ2_SHIFT ) )
#define PINMUX_TZ3_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_TZ3_SHIFT ) )
#define PINMUX_EPWM1SYNCI_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EPWM1SYNCI_SHIFT ) )

#define PINMUX_BALL_A4_HET1_16 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A4_SHIFT ) )
#define PINMUX_BALL_A4_ETPWM1SYNCI \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_A4_SHIFT ) )
#define PINMUX_BALL_A4_ETPWM1SYNCO \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_A4_SHIFT ) )

#define PINMUX_BALL_A5_GIOA_0 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A5_SHIFT ) )
#define PINMUX_BALL_A5_OHCI_PRT_RcvDpls_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_A5_SHIFT ) )
#define PINMUX_BALL_A5_W2FC_RXDPI \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_A5_SHIFT ) )

#define PINMUX_BALL_A11_HET1_14 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A11_SHIFT ) )
#define PINMUX_BALL_A11_OHCI_RCFG_txSe0_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_A11_SHIFT ) )

#define PINMUX_BALL_A14_HET1_26 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A14_SHIFT ) )
#define PINMUX_BALL_A14_MII_RXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_A14_SHIFT ) )
#define PINMUX_BALL_A14_RMII_RXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_A14_SHIFT ) )

#define PINMUX_BALL_B2_MIBSPI3NCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B2_I2C_SDA ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B2_HET1_27 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B2_nTZ2    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B2_SHIFT ) )

#define PINMUX_BALL_B3_HET1_22 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B3_SHIFT ) )
#define PINMUX_BALL_B3_OHCI_RCFG_txSe0_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B3_SHIFT ) )
#define PINMUX_BALL_B3_W2FC_SE0O \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B3_SHIFT ) )

#define PINMUX_BALL_B4_HET1_12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_B4_MII_CRS ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_B4_RMII_CRS_DV \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B4_SHIFT ) )

#define PINMUX_BALL_B5_GIOA_5   ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B5_SHIFT ) )
#define PINMUX_BALL_B5_EXTCLKIN ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B5_SHIFT ) )
#define PINMUX_BALL_B5_ETPWM1A  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B5_SHIFT ) )

#define PINMUX_BALL_B11_HET1_30 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_B11_MII_RX_DV \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_B11_OHCI_RCFG_speed_0 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_B11_EQEP2S ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B11_SHIFT ) )

#define PINMUX_BALL_B12_HET1_04 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B12_SHIFT ) )
#define PINMUX_BALL_B12_ETPWM4B \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B12_SHIFT ) )

#define PINMUX_BALL_C1_GIOA_2 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C1_OHCI_RCFG_txdPls_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C1_W2FC_TXDO \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C1_HET2_0 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C1_EQEP2I ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_C1_SHIFT ) )

#define PINMUX_BALL_C2_GIOA_1 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C2_SHIFT ) )
#define PINMUX_BALL_C2_OHCI_PRT_RcvDmns_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C2_SHIFT ) )
#define PINMUX_BALL_C2_W2FC_RXDMI \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C2_SHIFT ) )

#define PINMUX_BALL_C3_MIBSPI3NCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C3_I2C_SCL ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C3_HET1_29 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C3_nTZ1    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_C3_SHIFT ) )

#define PINMUX_BALL_C4_EMIF_ADDR_6 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C4_SHIFT ) )
#define PINMUX_BALL_C4_HET2_11 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C4_SHIFT ) )

#define PINMUX_BALL_C5_EMIF_ADDR_7 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C5_SHIFT ) )
#define PINMUX_BALL_C5_HET2_13 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C5_SHIFT ) )

#define PINMUX_BALL_C6_EMIF_ADDR_8 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C6_SHIFT ) )
#define PINMUX_BALL_C6_HET2_15  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C6_SHIFT ) )

#define PINMUX_BALL_D3_SPI2NENA ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D3_SHIFT ) )
#define PINMUX_BALL_D3_SPI2NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D3_SHIFT ) )

#define PINMUX_BALL_D4_EMIF_ADDR_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D4_SHIFT ) )
#define PINMUX_BALL_D4_HET2_1 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D4_SHIFT ) )

#define PINMUX_BALL_D5_EMIF_ADDR_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D5_SHIFT ) )
#define PINMUX_BALL_D5_HET2_3 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D5_SHIFT ) )

#define PINMUX_BALL_D16_EMIF_BA_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D16_SHIFT ) )
#define PINMUX_BALL_D16_HET2_5 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D16_SHIFT ) )

#define PINMUX_BALL_D17_EMIF_nWE \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D17_SHIFT ) )
#define PINMUX_BALL_D17_EMIF_RNW \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D17_SHIFT ) )

#define PINMUX_BALL_D19_HET1_10 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_MII_TX_CLK \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_OHCI_RCFG_txEnL_0 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_MII_TX_AVCLK4 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_nTZ3   ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_D19_SHIFT ) )

#define PINMUX_BALL_E1_GIOA_3  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E1_SHIFT ) )
#define PINMUX_BALL_E1_HET2_02 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E1_SHIFT ) )

#define PINMUX_BALL_E3_HET1_11 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_MIBSPI3NCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_HET2_18 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_OHCI_PRT_OvrCurrent_1 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_W2FC_VBUSI \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_ETPWM1SYNCO \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_E3_SHIFT ) )

#define PINMUX_BALL_E18_HET1_08 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_E18_MIBSPI1SIMO_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_E18_MII_TXD_3 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_E18_OHCI_PRT_OvrCurrent_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_E18_SHIFT ) )

#define PINMUX_BALL_E19_MIBSPI5NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E19_SHIFT ) )
#define PINMUX_BALL_E19_ETPWM4A \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_E19_SHIFT ) )

#define PINMUX_BALL_F3_MIBSPI1NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_HET1_17 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_MII_COL ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_OHCI_RCFG_suspend_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_EQEP1S ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_F3_SHIFT ) )

#define PINMUX_BALL_G3_MIBSPI1NCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G3_SHIFT ) )
#define PINMUX_BALL_G3_HET1_19 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_G3_SHIFT ) )
#define PINMUX_BALL_G3_MDIO    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_G3_SHIFT ) )

#define PINMUX_BALL_G19_MIBSPI1NENA \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_HET1_23 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_MII_RXD_2 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_OHCI_PRT_RcvDpls_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_ECAP4  ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_G19_SHIFT ) )

#define PINMUX_BALL_H3_GIOA_6  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H3_SHIFT ) )
#define PINMUX_BALL_H3_HET2_04 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_H3_SHIFT ) )
#define PINMUX_BALL_H3_ETPWM1B ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_H3_SHIFT ) )

#define PINMUX_BALL_H18_MIBSPI5NENA \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_MII_RXD_3 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_OHCI_PRT_RcvDmns_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_MIBSPI5SOMI_1 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_ECAP5 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_H18_SHIFT ) )

#define PINMUX_BALL_H19_MIBSPI5CLK \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_H19_MII_TXEN \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_H19_RMII_TXEN \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_H19_SHIFT ) )

#define PINMUX_BALL_J1_HET1_18 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J1_SHIFT ) )
#define PINMUX_BALL_J1_ETPWM6A ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J1_SHIFT ) )

#define PINMUX_BALL_J3_MIBSPI1NCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J3_SHIFT ) )
#define PINMUX_BALL_J3_HET1_21 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J3_SHIFT ) )

#define PINMUX_BALL_J18_MIBSPI5SOMI_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_J18_MII_TXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_J18_RMII_TXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_J18_SHIFT ) )

#define PINMUX_BALL_J19_MIBSPI5SIMO_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_J19_MII_TXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_J19_RMII_TXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_J19_MIBSPI5SOMI_2 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_J19_SHIFT ) )

#define PINMUX_BALL_K2_GIOB_1 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K2_SHIFT ) )
#define PINMUX_BALL_K2_OHCI_RCFG_PrtPower_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K2_SHIFT ) )

#define PINMUX_BALL_K17_EMIF_nCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K17_SHIFT ) )
#define PINMUX_BALL_K17_HET2_09 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_K17_SHIFT ) )

#define PINMUX_BALL_K18_HET1_0 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K18_SHIFT ) )
#define PINMUX_BALL_K18_SPI4CLK \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K18_SHIFT ) )
#define PINMUX_BALL_K18_ETPWM2B \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_K18_SHIFT ) )

#define PINMUX_BALL_K19_HET1_28 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_K19_MII_RXCLK \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_K19_RMII_REFCLK \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_K19_MII_RX_AVCLK4 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_K19_SHIFT ) )

#define PINMUX_BALL_M1_GIOA_7  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_M1_SHIFT ) )
#define PINMUX_BALL_M1_HET2_06 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_M1_SHIFT ) )
#define PINMUX_BALL_M1_ETPWM2A ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_M1_SHIFT ) )

#define PINMUX_BALL_M2_GIOB_0  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_M2_SHIFT ) )
#define PINMUX_BALL_M2_OHCI_RCFG_txDpls_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_M2_SHIFT ) )

#define PINMUX_BALL_N1_HET1_15 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_N1_MIBSPI1NCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_N1_ECAP1   ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N1_SHIFT ) )

#define PINMUX_BALL_N2_HET1_13 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N2_SCITX   ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N2_ETPWM5B ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N2_SHIFT ) )

#define PINMUX_BALL_N17_EMIF_nCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N17_SHIFT ) )
#define PINMUX_BALL_N17_HET2_07 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N17_SHIFT ) )

#define PINMUX_BALL_N19_AD1EVT ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_N19_MII_RX_ER \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_N19_RMII_RX_ER \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N19_SHIFT ) )

#define PINMUX_BALL_P1_HET1_24 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P1_MIBSPI1NCS_5 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P1_MII_RXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P1_RMII_RXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_P1_SHIFT ) )

#define PINMUX_BALL_P2_HET1_20 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P2_SHIFT ) )
#define PINMUX_BALL_P2_ETPWM6B ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_P2_SHIFT ) )

#define PINMUX_BALL_R2_MIBSPI1NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_MIBSPI1SOMI_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_MII_TXD_2 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_OHCI_PRT_RcvData_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_ECAP6   ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_R2_SHIFT ) )

#define PINMUX_BALL_T1_HET1_07 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_OHCI_RCFG_PrtPower_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_W2FC_GZO ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_HET2_14  ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_ETPWM7B  ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_T1_SHIFT ) )

#define PINMUX_BALL_U1_HET1_03  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_SPI4NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_OHCI_RCFG_speed_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_W2FC_PUENON \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_HET2_10  ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_EQEP2B   ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_U1_SHIFT ) )

#define PINMUX_BALL_V2_HET1_01  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_SPI4NENA ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_OHCI_RCFG_txEnL_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_W2FC_PUENO \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_HET2_08 ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_EQEP2A  ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V2_SHIFT ) )

#define PINMUX_BALL_V5_MIBSPI3NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V5_SHIFT ) )
#define PINMUX_BALL_V5_HET1_25  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V5_SHIFT ) )
#define PINMUX_BALL_V5_MDCLK    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V5_SHIFT ) )

#define PINMUX_BALL_V6_HET1_05  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V6_SPI4SOMI ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V6_HET2_12  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V6_ETPWM3B  ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V6_SHIFT ) )

#define PINMUX_BALL_V7_HET1_09  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_HET2_16  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_OHCI_RCFG_suspend_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_W2FC_SUSPENDO \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_ETPWM7A ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_V7_SHIFT ) )

#define PINMUX_BALL_V8_MIBSPI3SOMI \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V8_SHIFT ) )
#define PINMUX_BALL_V8_AWM_EXT_ENA \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V8_SHIFT ) )
#define PINMUX_BALL_V8_ECAP2 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V8_SHIFT ) )

#define PINMUX_BALL_V9_MIBSPI3CLK \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V9_SHIFT ) )
#define PINMUX_BALL_V9_AWM_EXT_SEL_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V9_SHIFT ) )
#define PINMUX_BALL_V9_EQEP1A ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V9_SHIFT ) )

#define PINMUX_BALL_V10_MIBSPI3NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_V10_AD2EVT  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_V10_GIOB_2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_V10_EQEP1I  ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V10_SHIFT ) )

#define PINMUX_BALL_W3_HET1_06  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W3_SHIFT ) )
#define PINMUX_BALL_W3_SCIRX    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W3_SHIFT ) )
#define PINMUX_BALL_W3_ETPWM5A  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_W3_SHIFT ) )

#define PINMUX_BALL_W5_HET1_02  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W5_SHIFT ) )
#define PINMUX_BALL_W5_SPI4SIMO ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W5_SHIFT ) )
#define PINMUX_BALL_W5_ETPWM3A  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_W5_SHIFT ) )

#define PINMUX_BALL_W8_MIBSPI3SIMO \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W8_SHIFT ) )
#define PINMUX_BALL_W8_AWM_EXT_SEL_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W8_SHIFT ) )
#define PINMUX_BALL_W8_ECAP3 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_W8_SHIFT ) )

#define PINMUX_BALL_W9_MIBSPI3NENA \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W9_MIBSPI3NCS_5 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W9_HET1_31 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W9_EQEP1B  ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_W9_SHIFT ) )

#define PINMUX_BALL_W10_GIOB_3 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W10_SHIFT ) )
#define PINMUX_BALL_W10_OHCI_PRT_RcvData_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W10_SHIFT ) )
#define PINMUX_BALL_W10_W2FC_RXDI \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_W10_SHIFT ) )

#define PINMUX_GATE_EMIF_CLK_ON \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GATE_EMIF_CLK_SHIFT ) )
#define PINMUX_GIOB_DISABLE_HET2_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB_DISABLE_HET2_SHIFT ) )
#define PINMUX_GATE_EMIF_CLK_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GATE_EMIF_CLK_SHIFT ) )
#define PINMUX_GIOB_DISABLE_HET2_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB_DISABLE_HET2_SHIFT ) )
#define PINMUX_ALT_ADC_TRIGGER_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ALT_ADC_TRIGGER_SHIFT ) )
#define PINMUX_ALT_ADC_TRIGGER_2 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ALT_ADC_TRIGGER_SHIFT ) )
#define PINMUX_ETHERNET_MII     ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETHERNET_SHIFT ) )
#define PINMUX_ETHERNET_RMII    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETHERNET_SHIFT ) )

#define PINMUX_ETPWM1_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM1_SHIFT ) )
#define PINMUX_ETPWM1_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM1_SHIFT ) )
#define PINMUX_ETPWM1_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM1_SHIFT ) )
#define PINMUX_ETPWM2_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM2_SHIFT ) )
#define PINMUX_ETPWM2_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM2_SHIFT ) )
#define PINMUX_ETPWM2_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM2_SHIFT ) )
#define PINMUX_ETPWM3_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM3_SHIFT ) )
#define PINMUX_ETPWM3_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM3_SHIFT ) )
#define PINMUX_ETPWM3_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM3_SHIFT ) )
#define PINMUX_ETPWM4_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM4_SHIFT ) )
#define PINMUX_ETPWM4_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM4_SHIFT ) )
#define PINMUX_ETPWM4_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM4_SHIFT ) )
#define PINMUX_ETPWM5_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM5_SHIFT ) )
#define PINMUX_ETPWM5_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM5_SHIFT ) )
#define PINMUX_ETPWM5_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM5_SHIFT ) )
#define PINMUX_ETPWM6_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM6_SHIFT ) )
#define PINMUX_ETPWM6_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM6_SHIFT ) )
#define PINMUX_ETPWM6_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM6_SHIFT ) )
#define PINMUX_ETPWM7_EQEPERR12 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM7_SHIFT ) )
#define PINMUX_ETPWM7_EQEPERR1  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM7_SHIFT ) )
#define PINMUX_ETPWM7_EQEPERR2  ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_ETPWM7_SHIFT ) )
#define PINMUX_ETPWM_TIME_BASE_SYNC_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM_TIME_BASE_SYNC_SHIFT ) )
#define PINMUX_ETPWM_TBCLK_SYNC_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ETPWM_TBCLK_SYNC_SHIFT ) )
#define PINMUX_ETPWM_TIME_BASE_SYNC_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_TIME_BASE_SYNC_SHIFT ) )
#define PINMUX_ETPWM_TBCLK_SYNC_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_TBCLK_SYNC_SHIFT ) )
#define PINMUX_TZ1_ASYNC    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_TZ1_SHIFT ) )
#define PINMUX_TZ1_SYNC     ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_TZ1_SHIFT ) )
#define PINMUX_TZ1_FILTERED ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_TZ1_SHIFT ) )
#define PINMUX_TZ2_ASYNC    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_TZ2_SHIFT ) )
#define PINMUX_TZ2_SYNC     ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_TZ2_SHIFT ) )
#define PINMUX_TZ2_FILTERED ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_TZ2_SHIFT ) )
#define PINMUX_TZ3_ASYNC    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_TZ3_SHIFT ) )
#define PINMUX_TZ3_SYNC     ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_TZ3_SHIFT ) )
#define PINMUX_TZ3_FILTERED ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_TZ3_SHIFT ) )
#define PINMUX_EPWM1SYNCI_ASYNC \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_EPWM1SYNCI_SHIFT ) )
#define PINMUX_EPWM1SYNCI_SYNC \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EPWM1SYNCI_SHIFT ) )
#define PINMUX_EPWM1SYNCI_FILTERED \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_EPWM1SYNCI_SHIFT ) )

typedef struct pinmux_config_reg
{
    uint32 CONFIG_PINMMR0;
    uint32 CONFIG_PINMMR1;
    uint32 CONFIG_PINMMR2;
    uint32 CONFIG_PINMMR3;
    uint32 CONFIG_PINMMR4;
    uint32 CONFIG_PINMMR5;
    uint32 CONFIG_PINMMR6;
    uint32 CONFIG_PINMMR7;
    uint32 CONFIG_PINMMR8;
    uint32 CONFIG_PINMMR9;
    uint32 CONFIG_PINMMR10;
    uint32 CONFIG_PINMMR11;
    uint32 CONFIG_PINMMR12;
    uint32 CONFIG_PINMMR13;
    uint32 CONFIG_PINMMR14;
    uint32 CONFIG_PINMMR15;
    uint32 CONFIG_PINMMR16;
    uint32 CONFIG_PINMMR17;
    uint32 CONFIG_PINMMR18;
    uint32 CONFIG_PINMMR19;
    uint32 CONFIG_PINMMR20;
    uint32 CONFIG_PINMMR21;
    uint32 CONFIG_PINMMR22;
    uint32 CONFIG_PINMMR23;
    uint32 CONFIG_PINMMR24;
    uint32 CONFIG_PINMMR25;
    uint32 CONFIG_PINMMR26;
    uint32 CONFIG_PINMMR27;
    uint32 CONFIG_PINMMR28;
    uint32 CONFIG_PINMMR29;
    uint32 CONFIG_PINMMR30;
    uint32 CONFIG_PINMMR31;
    uint32 CONFIG_PINMMR32;
    uint32 CONFIG_PINMMR33;
    uint32 CONFIG_PINMMR34;
    uint32 CONFIG_PINMMR35;
    uint32 CONFIG_PINMMR36;
    uint32 CONFIG_PINMMR37;
    uint32 CONFIG_PINMMR38;
    uint32 CONFIG_PINMMR39;
    uint32 CONFIG_PINMMR40;
    uint32 CONFIG_PINMMR41;
    uint32 CONFIG_PINMMR42;
    uint32 CONFIG_PINMMR43;
    uint32 CONFIG_PINMMR44;
    uint32 CONFIG_PINMMR45;
    uint32 CONFIG_PINMMR46;
    uint32 CONFIG_PINMMR47;
} pinmux_config_reg_t;

/**
 *  @defgroup IOMM IOMM
 *  @brief I/O Multiplexing and Control Module.
 *
 *  The IOMM contains memory-mapped registers (MMR) that control device-specific
 * multiplexed functions. The safety and diagnostic features of the IOMM are:
 *  - Kicker mechanism to protect the MMRs from accidental writes
 *  - Master-id checker to only allow the CPU to write to the MMRs
 *  - Error indication for access violations
 *
 *  Related Files
 *   - reg_pinmux.h
 *   - pinmux.h
 *   - pinmux.c
 *  @addtogroup IOMM
 *  @{
 */

/** @fn void muxInit(void)
 *   @brief Initializes the PINMUX Driver
 *
 *   This function initializes the PINMUX module and configures the selected
 *   pinmux settings as per the user selection in the GUI
 */
void muxInit( void );
void pinmuxGetConfigValue( pinmux_config_reg_t * config_reg, config_value_type_t type );
/* USER CODE BEGIN (0) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */
#endif /* ifndef __PINMUX_H__ */
