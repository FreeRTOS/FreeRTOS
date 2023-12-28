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

/* USER CODE BEGIN (0) */
/* USER CODE END */

#define PINMUX_BALL_N19_SHIFT             0U
#define PINMUX_BALL_D4_SHIFT              8U
#define PINMUX_BALL_D5_SHIFT              16U
#define PINMUX_BALL_C4_SHIFT              24U
#define PINMUX_BALL_C5_SHIFT              0U
#define PINMUX_BALL_C6_SHIFT              8U
#define PINMUX_BALL_C7_SHIFT              16U
#define PINMUX_BALL_C8_SHIFT              24U
#define PINMUX_BALL_C9_SHIFT              0U
#define PINMUX_BALL_C10_SHIFT             8U
#define PINMUX_BALL_C11_SHIFT             16U
#define PINMUX_BALL_C12_SHIFT             24U
#define PINMUX_BALL_C13_SHIFT             0U
#define PINMUX_BALL_D14_SHIFT             8U
#define PINMUX_BALL_C14_SHIFT             16U
#define PINMUX_BALL_D15_SHIFT             24U
#define PINMUX_BALL_C15_SHIFT             0U
#define PINMUX_BALL_C16_SHIFT             8U
#define PINMUX_BALL_C17_SHIFT             16U
#define PINMUX_BALL_D16_SHIFT             24U
#define PINMUX_BALL_K3_SHIFT              0U
#define PINMUX_BALL_R4_SHIFT              8U
#define PINMUX_BALL_N17_SHIFT             16U
#define PINMUX_BALL_L17_SHIFT             24U
#define PINMUX_BALL_K17_SHIFT             0U
#define PINMUX_BALL_M17_SHIFT             8U
#define PINMUX_BALL_R3_SHIFT              16U
#define PINMUX_BALL_P3_SHIFT              24U
#define PINMUX_BALL_D17_SHIFT             0U
#define PINMUX_BALL_E9_SHIFT              8U
#define PINMUX_BALL_E8_SHIFT              16U
#define PINMUX_BALL_E7_SHIFT              24U
#define PINMUX_BALL_E6_SHIFT              0U
#define PINMUX_BALL_E13_SHIFT             8U
#define PINMUX_BALL_E12_SHIFT             16U
#define PINMUX_BALL_E11_SHIFT             24U
#define PINMUX_BALL_E10_SHIFT             0U
#define PINMUX_BALL_K15_SHIFT             8U
#define PINMUX_BALL_L15_SHIFT             16U
#define PINMUX_BALL_M15_SHIFT             24U
#define PINMUX_BALL_N15_SHIFT             0U
#define PINMUX_BALL_E5_SHIFT              8U
#define PINMUX_BALL_F5_SHIFT              16U
#define PINMUX_BALL_G5_SHIFT              24U
#define PINMUX_BALL_K5_SHIFT              0U
#define PINMUX_BALL_L5_SHIFT              8U
#define PINMUX_BALL_M5_SHIFT              16U
#define PINMUX_BALL_N5_SHIFT              24U
#define PINMUX_BALL_P5_SHIFT              0U
#define PINMUX_BALL_R5_SHIFT              8U
#define PINMUX_BALL_R6_SHIFT              16U
#define PINMUX_BALL_R7_SHIFT              24U
#define PINMUX_BALL_R8_SHIFT              0U
#define PINMUX_BALL_R9_SHIFT              8U
#define PINMUX_BALL_R10_SHIFT             16U
#define PINMUX_BALL_R11_SHIFT             24U
#define PINMUX_BALL_B15_SHIFT             0U
#define PINMUX_BALL_B8_SHIFT              8U
#define PINMUX_BALL_B16_SHIFT             16U
#define PINMUX_BALL_B9_SHIFT              24U
#define PINMUX_BALL_C1_SHIFT              0U
#define PINMUX_BALL_E1_SHIFT              8U
#define PINMUX_BALL_B5_SHIFT              16U
#define PINMUX_BALL_H3_SHIFT              24U
#define PINMUX_BALL_M1_SHIFT              0U
#define PINMUX_BALL_F2_SHIFT              8U
#define PINMUX_BALL_W10_SHIFT             16U
#define PINMUX_BALL_J2_SHIFT              24U
#define PINMUX_BALL_F1_SHIFT              0U
#define PINMUX_BALL_R2_SHIFT              8U
#define PINMUX_BALL_F3_SHIFT              16U
#define PINMUX_BALL_G3_SHIFT              24U
#define PINMUX_BALL_J3_SHIFT              0U
#define PINMUX_BALL_G19_SHIFT             8U
#define PINMUX_BALL_V9_SHIFT              16U
#define PINMUX_BALL_V10_SHIFT             24U
#define PINMUX_BALL_V5_SHIFT              0U
#define PINMUX_BALL_B2_SHIFT              8U
#define PINMUX_BALL_C3_SHIFT              16U
#define PINMUX_BALL_W9_SHIFT              24U
#define PINMUX_BALL_W8_SHIFT              0U
#define PINMUX_BALL_V8_SHIFT              8U
#define PINMUX_BALL_H19_SHIFT             16U
#define PINMUX_BALL_E19_SHIFT             24U
#define PINMUX_BALL_B6_SHIFT              0U
#define PINMUX_BALL_W6_SHIFT              8U
#define PINMUX_BALL_T12_SHIFT             16U
#define PINMUX_BALL_H18_SHIFT             24U
#define PINMUX_BALL_J19_SHIFT             0U
#define PINMUX_BALL_E16_SHIFT             8U
#define PINMUX_BALL_H17_SHIFT             16U
#define PINMUX_BALL_G17_SHIFT             24U
#define PINMUX_BALL_J18_SHIFT             0U
#define PINMUX_BALL_E17_SHIFT             8U
#define PINMUX_BALL_H16_SHIFT             16U
#define PINMUX_BALL_G16_SHIFT             24U
#define PINMUX_BALL_K18_SHIFT             0U
#define PINMUX_BALL_V2_SHIFT              8U
#define PINMUX_BALL_W5_SHIFT              16U
#define PINMUX_BALL_U1_SHIFT              24U
#define PINMUX_BALL_B12_SHIFT             0U
#define PINMUX_BALL_V6_SHIFT              8U
#define PINMUX_BALL_W3_SHIFT              16U
#define PINMUX_BALL_T1_SHIFT              24U
#define PINMUX_BALL_E18_SHIFT             0U
#define PINMUX_BALL_V7_SHIFT              8U
#define PINMUX_BALL_D19_SHIFT             16U
#define PINMUX_BALL_E3_SHIFT              24U
#define PINMUX_BALL_B4_SHIFT              0U
#define PINMUX_BALL_N2_SHIFT              8U
#define PINMUX_BALL_N1_SHIFT              16U
#define PINMUX_BALL_A4_SHIFT              24U
#define PINMUX_BALL_A13_SHIFT             0U
#define PINMUX_BALL_J1_SHIFT              8U
#define PINMUX_BALL_B13_SHIFT             16U
#define PINMUX_BALL_P2_SHIFT              24U
#define PINMUX_BALL_H4_SHIFT              0U
#define PINMUX_BALL_B3_SHIFT              8U
#define PINMUX_BALL_J4_SHIFT              16U
#define PINMUX_BALL_P1_SHIFT              24U
#define PINMUX_BALL_A14_SHIFT             0U
#define PINMUX_BALL_K19_SHIFT             8U
#define PINMUX_BALL_B11_SHIFT             16U
#define PINMUX_BALL_D8_SHIFT              24U
#define PINMUX_BALL_D7_SHIFT              0U
#define PINMUX_BALL_D3_SHIFT              8U
#define PINMUX_BALL_D2_SHIFT              16U
#define PINMUX_BALL_D1_SHIFT              24U
#define PINMUX_BALL_P4_SHIFT              0U
#define PINMUX_BALL_T5_SHIFT              8U
#define PINMUX_BALL_T4_SHIFT              16U
#define PINMUX_BALL_U7_SHIFT              24U
#define PINMUX_BALL_E2_SHIFT              0U
#define PINMUX_BALL_N3_SHIFT              8U

#define PINMUX_GATE_EMIF_CLK_SHIFT        0U
#define PINMUX_EMIF_OUTPUT_ENABLE_SHIFT   8U
#define PINMUX_GIOA_DISABLE_HET1_SHIFT    8U
#define PINMUX_GIOB_DISABLE_HET2_SHIFT    0U
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
#define PINMUX_ETPWM_SOC1A_SHIFT          0U
#define PINMUX_ETPWM_SOC2A_SHIFT          8U
#define PINMUX_ETPWM_SOC3A_SHIFT          16U
#define PINMUX_ETPWM_SOC4A_SHIFT          24U
#define PINMUX_ETPWM_SOC5A_SHIFT          0U
#define PINMUX_ETPWM_SOC6A_SHIFT          8U
#define PINMUX_ETPWM_SOC7A_SHIFT          16U
#define PINMUX_EQEP1A_FILTER_SHIFT        16U
#define PINMUX_EQEP1B_FILTER_SHIFT        24U
#define PINMUX_EQEP1I_FILTER_SHIFT        0U
#define PINMUX_EQEP1S_FILTER_SHIFT        8U
#define PINMUX_EQEP2A_FILTER_SHIFT        16U
#define PINMUX_EQEP2B_FILTER_SHIFT        24U
#define PINMUX_EQEP2I_FILTER_SHIFT        0U
#define PINMUX_EQEP2S_FILTER_SHIFT        8U
#define PINMUX_ECAP1_FILTER_SHIFT         0U
#define PINMUX_ECAP2_FILTER_SHIFT         8U
#define PINMUX_ECAP3_FILTER_SHIFT         16U
#define PINMUX_ECAP4_FILTER_SHIFT         24U
#define PINMUX_ECAP5_FILTER_SHIFT         0U
#define PINMUX_ECAP6_FILTER_SHIFT         8U
#define PINMUX_GIOA0_DMA_SHIFT            0U
#define PINMUX_GIOA1_DMA_SHIFT            8U
#define PINMUX_GIOA2_DMA_SHIFT            16U
#define PINMUX_GIOA3_DMA_SHIFT            24U
#define PINMUX_GIOA4_DMA_SHIFT            0U
#define PINMUX_GIOA5_DMA_SHIFT            8U
#define PINMUX_GIOA6_DMA_SHIFT            16U
#define PINMUX_GIOA7_DMA_SHIFT            24U
#define PINMUX_GIOB0_DMA_SHIFT            0U
#define PINMUX_GIOB1_DMA_SHIFT            8U
#define PINMUX_GIOB2_DMA_SHIFT            16U
#define PINMUX_GIOB3_DMA_SHIFT            24U
#define PINMUX_GIOB4_DMA_SHIFT            0U
#define PINMUX_GIOB5_DMA_SHIFT            8U
#define PINMUX_GIOB6_DMA_SHIFT            16U
#define PINMUX_GIOB7_DMA_SHIFT            24U
#define PINMUX_TEMP1_ENABLE_SHIFT         16U
#define PINMUX_TEMP2_ENABLE_SHIFT         24U
#define PINMUX_TEMP3_ENABLE_SHIFT         0U

#define PINMUX_BALL_N19_MASK \
    ( ~( uint32 ) ( ( uint32 ) uint32 )( ( uint32 ) 0xFFU << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_D4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D4_SHIFT ) )
#define PINMUX_BALL_D5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D5_SHIFT ) )
#define PINMUX_BALL_C4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C4_SHIFT ) )
#define PINMUX_BALL_C5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C5_SHIFT ) )
#define PINMUX_BALL_C6_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C6_SHIFT ) )
#define PINMUX_BALL_C7_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C7_SHIFT ) )
#define PINMUX_BALL_C8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C8_SHIFT ) )
#define PINMUX_BALL_C9_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C9_SHIFT ) )
#define PINMUX_BALL_C10_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C10_SHIFT ) )
#define PINMUX_BALL_C11_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C11_SHIFT ) )
#define PINMUX_BALL_C12_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C12_SHIFT ) )
#define PINMUX_BALL_C13_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C13_SHIFT ) )
#define PINMUX_BALL_D14_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D14_SHIFT ) )
#define PINMUX_BALL_C14_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C14_SHIFT ) )
#define PINMUX_BALL_D15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D15_SHIFT ) )
#define PINMUX_BALL_C15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C15_SHIFT ) )
#define PINMUX_BALL_C16_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C16_SHIFT ) )
#define PINMUX_BALL_C17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C17_SHIFT ) )
#define PINMUX_BALL_D16_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D16_SHIFT ) )
#define PINMUX_BALL_K3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K3_SHIFT ) )
#define PINMUX_BALL_R4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R4_SHIFT ) )
#define PINMUX_BALL_N17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N17_SHIFT ) )
#define PINMUX_BALL_L17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_L17_SHIFT ) )
#define PINMUX_BALL_K17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K17_SHIFT ) )
#define PINMUX_BALL_M17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_M17_SHIFT ) )
#define PINMUX_BALL_R3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R3_SHIFT ) )
#define PINMUX_BALL_P3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P3_SHIFT ) )
#define PINMUX_BALL_D17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D17_SHIFT ) )
#define PINMUX_BALL_E9_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E9_SHIFT ) )
#define PINMUX_BALL_E8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E8_SHIFT ) )
#define PINMUX_BALL_E7_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E7_SHIFT ) )
#define PINMUX_BALL_E6_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E6_SHIFT ) )
#define PINMUX_BALL_E13_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E13_SHIFT ) )
#define PINMUX_BALL_E12_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E12_SHIFT ) )
#define PINMUX_BALL_E11_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E11_SHIFT ) )
#define PINMUX_BALL_E10_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E10_SHIFT ) )
#define PINMUX_BALL_K15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K15_SHIFT ) )
#define PINMUX_BALL_L15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_L15_SHIFT ) )
#define PINMUX_BALL_M15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_M15_SHIFT ) )
#define PINMUX_BALL_N15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N15_SHIFT ) )
#define PINMUX_BALL_E5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E5_SHIFT ) )
#define PINMUX_BALL_F5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_F5_SHIFT ) )
#define PINMUX_BALL_G5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G5_SHIFT ) )
#define PINMUX_BALL_K5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K5_SHIFT ) )
#define PINMUX_BALL_L5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_L5_SHIFT ) )
#define PINMUX_BALL_M5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_M5_SHIFT ) )
#define PINMUX_BALL_N5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N5_SHIFT ) )
#define PINMUX_BALL_P5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P5_SHIFT ) )
#define PINMUX_BALL_R5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R5_SHIFT ) )
#define PINMUX_BALL_R6_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R6_SHIFT ) )
#define PINMUX_BALL_R7_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R7_SHIFT ) )
#define PINMUX_BALL_R8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R8_SHIFT ) )
#define PINMUX_BALL_R9_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R9_SHIFT ) )
#define PINMUX_BALL_R10_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R10_SHIFT ) )
#define PINMUX_BALL_R11_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R11_SHIFT ) )
#define PINMUX_BALL_B15_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B15_SHIFT ) )
#define PINMUX_BALL_B8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B8_SHIFT ) )
#define PINMUX_BALL_B16_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B16_SHIFT ) )
#define PINMUX_BALL_B9_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B9_SHIFT ) )
#define PINMUX_BALL_C1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_E1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E1_SHIFT ) )
#define PINMUX_BALL_B5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B5_SHIFT ) )
#define PINMUX_BALL_H3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H3_SHIFT ) )
#define PINMUX_BALL_M1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_M1_SHIFT ) )
#define PINMUX_BALL_F2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_F2_SHIFT ) )
#define PINMUX_BALL_W10_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W10_SHIFT ) )
#define PINMUX_BALL_J2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J2_SHIFT ) )
#define PINMUX_BALL_F1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_F1_SHIFT ) )
#define PINMUX_BALL_R2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_F3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_G3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G3_SHIFT ) )
#define PINMUX_BALL_J3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J3_SHIFT ) )
#define PINMUX_BALL_G19_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_V9_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V9_SHIFT ) )
#define PINMUX_BALL_V10_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_V5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V5_SHIFT ) )
#define PINMUX_BALL_B2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_C3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_W9_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W8_SHIFT ) )
#define PINMUX_BALL_V8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V8_SHIFT ) )
#define PINMUX_BALL_H19_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_E19_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E19_SHIFT ) )
#define PINMUX_BALL_B6_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B6_SHIFT ) )
#define PINMUX_BALL_W6_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W6_SHIFT ) )
#define PINMUX_BALL_T12_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_T12_SHIFT ) )
#define PINMUX_BALL_H18_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_J19_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_E16_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E16_SHIFT ) )
#define PINMUX_BALL_H17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H17_SHIFT ) )
#define PINMUX_BALL_G17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G17_SHIFT ) )
#define PINMUX_BALL_J18_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_E17_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E17_SHIFT ) )
#define PINMUX_BALL_H16_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H16_SHIFT ) )
#define PINMUX_BALL_G16_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_G16_SHIFT ) )
#define PINMUX_BALL_K18_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K18_SHIFT ) )
#define PINMUX_BALL_V2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_W5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W5_SHIFT ) )
#define PINMUX_BALL_U1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_B12_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B12_SHIFT ) )
#define PINMUX_BALL_V6_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_W3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_W3_SHIFT ) )
#define PINMUX_BALL_T1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_E18_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_V7_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_D19_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_E3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_B4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_N2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_A4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A4_SHIFT ) )
#define PINMUX_BALL_A13_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A13_SHIFT ) )
#define PINMUX_BALL_J1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J1_SHIFT ) )
#define PINMUX_BALL_B13_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B13_SHIFT ) )
#define PINMUX_BALL_P2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P2_SHIFT ) )
#define PINMUX_BALL_H4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_H4_SHIFT ) )
#define PINMUX_BALL_B3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B3_SHIFT ) )
#define PINMUX_BALL_J4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_J4_SHIFT ) )
#define PINMUX_BALL_P1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_A14_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_A14_SHIFT ) )
#define PINMUX_BALL_K19_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_B11_MASK ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_D8_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D8_SHIFT ) )
#define PINMUX_BALL_D7_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D7_SHIFT ) )
#define PINMUX_BALL_D3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D3_SHIFT ) )
#define PINMUX_BALL_D2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D2_SHIFT ) )
#define PINMUX_BALL_D1_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_D1_SHIFT ) )
#define PINMUX_BALL_P4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_P4_SHIFT ) )
#define PINMUX_BALL_T5_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_T5_SHIFT ) )
#define PINMUX_BALL_T4_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_T4_SHIFT ) )
#define PINMUX_BALL_U7_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_U7_SHIFT ) )
#define PINMUX_BALL_E2_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_E2_SHIFT ) )
#define PINMUX_BALL_N3_MASK  ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_BALL_N3_SHIFT ) )

#define PINMUX_GATE_EMIF_CLK_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GATE_EMIF_CLK_SHIFT ) )
#define PINMUX_EMIF_OUTPUT_ENABLE_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EMIF_OUTPUT_ENABLE_SHIFT ) )
#define PINMUX_GIOA_DISABLE_HET1_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA_DISABLE_HET1_SHIFT ) )
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
#define PINMUX_ETPWM_SOC1A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC1A_SHIFT ) )
#define PINMUX_ETPWM_SOC2A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC2A_SHIFT ) )
#define PINMUX_ETPWM_SOC3A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC3A_SHIFT ) )
#define PINMUX_ETPWM_SOC4A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC4A_SHIFT ) )
#define PINMUX_ETPWM_SOC5A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC5A_SHIFT ) )
#define PINMUX_ETPWM_SOC6A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC6A_SHIFT ) )
#define PINMUX_ETPWM_SOC7A_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ETPWM_SOC7A_SHIFT ) )
#define PINMUX_EQEP1A_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP1A_FILTER_SHIFT ) )
#define PINMUX_EQEP1B_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP1B_FILTER_SHIFT ) )
#define PINMUX_EQEP1I_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP1I_FILTER_SHIFT ) )
#define PINMUX_EQEP1S_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP1S_FILTER_SHIFT ) )
#define PINMUX_EQEP2A_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP2A_FILTER_SHIFT ) )
#define PINMUX_EQEP2B_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP2B_FILTER_SHIFT ) )
#define PINMUX_EQEP2I_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP2I_FILTER_SHIFT ) )
#define PINMUX_EQEP2S_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_EQEP2S_FILTER_SHIFT ) )
#define PINMUX_ECAP1_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ECAP1_FILTER_SHIFT ) )
#define PINMUX_ECAP2_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ECAP2_FILTER_SHIFT ) )
#define PINMUX_ECAP3_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ECAP3_FILTER_SHIFT ) )
#define PINMUX_ECAP4_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ECAP4_FILTER_SHIFT ) )
#define PINMUX_ECAP5_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ECAP5_FILTER_SHIFT ) )
#define PINMUX_ECAP6_FILTER_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_ECAP6_FILTER_SHIFT ) )

#define PINMUX_GIOA0_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA0_DMA_SHIFT ) )
#define PINMUX_GIOA1_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA1_DMA_SHIFT ) )
#define PINMUX_GIOA2_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA2_DMA_SHIFT ) )
#define PINMUX_GIOA3_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA3_DMA_SHIFT ) )
#define PINMUX_GIOA4_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA4_DMA_SHIFT ) )
#define PINMUX_GIOA5_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA5_DMA_SHIFT ) )
#define PINMUX_GIOA6_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA6_DMA_SHIFT ) )
#define PINMUX_GIOA7_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOA7_DMA_SHIFT ) )
#define PINMUX_GIOB0_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB0_DMA_SHIFT ) )
#define PINMUX_GIOB1_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB1_DMA_SHIFT ) )
#define PINMUX_GIOB2_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB2_DMA_SHIFT ) )
#define PINMUX_GIOB3_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB3_DMA_SHIFT ) )
#define PINMUX_GIOB4_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB4_DMA_SHIFT ) )
#define PINMUX_GIOB5_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB5_DMA_SHIFT ) )
#define PINMUX_GIOB6_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB6_DMA_SHIFT ) )
#define PINMUX_GIOB7_DMA_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_GIOB7_DMA_SHIFT ) )
#define PINMUX_TEMP1_ENABLE_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_TEMP1_ENABLE_SHIFT ) )
#define PINMUX_TEMP2_ENABLE_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_TEMP2_ENABLE_SHIFT ) )
#define PINMUX_TEMP3_ENABLE_MASK \
    ( ~( uint32 ) ( ( uint32 ) 0xFFU << PINMUX_TEMP3_ENABLE_SHIFT ) )

#define PINMUX_BALL_N19_AD1EVT ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_N19_MII_RX_ER \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_N19_RMII_RX_ER \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_N19_SHIFT ) )
#define PINMUX_BALL_N19_nTZ1_1 \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_N19_SHIFT ) )

#define PINMUX_BALL_D4_EMIF_ADDR_00 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D4_SHIFT ) )
#define PINMUX_BALL_D4_N2HET2_01 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_D4_SHIFT ) )

#define PINMUX_BALL_D5_EMIF_ADDR_01 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D5_SHIFT ) )
#define PINMUX_BALL_D5_N2HET2_03 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_D5_SHIFT ) )

#define PINMUX_BALL_C4_EMIF_ADDR_06 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C4_SHIFT ) )
#define PINMUX_BALL_C4_RTP_DATA_13 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C4_SHIFT ) )
#define PINMUX_BALL_C4_N2HET2_11 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C4_SHIFT ) )

#define PINMUX_BALL_C5_EMIF_ADDR_07 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C5_SHIFT ) )
#define PINMUX_BALL_C5_RTP_DATA_12 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C5_SHIFT ) )
#define PINMUX_BALL_C5_N2HET2_13 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C5_SHIFT ) )

#define PINMUX_BALL_C6_EMIF_ADDR_08 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C6_SHIFT ) )
#define PINMUX_BALL_C6_RTP_DATA_11 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C6_SHIFT ) )
#define PINMUX_BALL_C6_N2HET2_15 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C6_SHIFT ) )

#define PINMUX_BALL_C7_EMIF_ADDR_09 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C7_SHIFT ) )
#define PINMUX_BALL_C7_RTP_DATA_10 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C7_SHIFT ) )

#define PINMUX_BALL_C8_EMIF_ADDR_10 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C8_SHIFT ) )
#define PINMUX_BALL_C8_RTP_DATA_09 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C8_SHIFT ) )

#define PINMUX_BALL_C9_EMIF_ADDR_11 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C9_SHIFT ) )
#define PINMUX_BALL_C9_RTP_DATA_08 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C9_SHIFT ) )

#define PINMUX_BALL_C10_EMIF_ADDR_12 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C10_SHIFT ) )
#define PINMUX_BALL_C10_RTP_DATA_06 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C10_SHIFT ) )

#define PINMUX_BALL_C11_EMIF_ADDR_13 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C11_SHIFT ) )
#define PINMUX_BALL_C11_RTP_DATA_05 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C11_SHIFT ) )

#define PINMUX_BALL_C12_EMIF_ADDR_14 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C12_SHIFT ) )
#define PINMUX_BALL_C12_RTP_DATA_04 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C12_SHIFT ) )

#define PINMUX_BALL_C13_EMIF_ADDR_15 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C13_SHIFT ) )
#define PINMUX_BALL_C13_RTP_DATA_03 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C13_SHIFT ) )

#define PINMUX_BALL_D14_EMIF_ADDR_16 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D14_SHIFT ) )
#define PINMUX_BALL_D14_RTP_DATA_02 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D14_SHIFT ) )

#define PINMUX_BALL_C14_EMIF_ADDR_17 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C14_SHIFT ) )
#define PINMUX_BALL_C14_RTP_DATA_01 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C14_SHIFT ) )

#define PINMUX_BALL_D15_EMIF_ADDR_18 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D15_SHIFT ) )
#define PINMUX_BALL_D15_RTP_DATA_00 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D15_SHIFT ) )

#define PINMUX_BALL_C15_EMIF_ADDR_19 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C15_SHIFT ) )
#define PINMUX_BALL_C15_RTP_nENA \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C15_SHIFT ) )

#define PINMUX_BALL_C16_EMIF_ADDR_20 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C16_SHIFT ) )
#define PINMUX_BALL_C16_RTP_nSYNC \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C16_SHIFT ) )

#define PINMUX_BALL_C17_EMIF_ADDR_21 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C17_SHIFT ) )
#define PINMUX_BALL_C17_RTP_CLK \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C17_SHIFT ) )

#define PINMUX_BALL_D16_EMIF_BA_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D16_SHIFT ) )
#define PINMUX_BALL_D16_8_25 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D16_SHIFT ) )
#define PINMUX_BALL_D16_N2HET2_05 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_D16_SHIFT ) )

#define PINMUX_BALL_K3_RESERVED ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K3_SHIFT ) )
#define PINMUX_BALL_K3_EMIF_CLK ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K3_SHIFT ) )
#define PINMUX_BALL_K3_ECLK2    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_K3_SHIFT ) )

#define PINMUX_BALL_R4_EMIF_nCAS \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R4_SHIFT ) )
#define PINMUX_BALL_R4_GIOB_3 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R4_SHIFT ) )

#define PINMUX_BALL_N17_EMIF_nCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N17_SHIFT ) )
#define PINMUX_BALL_N17_RTP_DATA_15 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N17_SHIFT ) )
#define PINMUX_BALL_N17_N2HET2_07 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N17_SHIFT ) )

#define PINMUX_BALL_L17_EMIF_nCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_L17_SHIFT ) )
#define PINMUX_BALL_L17_GIOB_4 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_L17_SHIFT ) )

#define PINMUX_BALL_K17_EMIF_nCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K17_SHIFT ) )
#define PINMUX_BALL_K17_RTP_DATA_14 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K17_SHIFT ) )
#define PINMUX_BALL_K17_N2HET2_09 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_K17_SHIFT ) )

#define PINMUX_BALL_M17_EMIF_nCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_M17_SHIFT ) )
#define PINMUX_BALL_M17_RTP_DATA_07 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_M17_SHIFT ) )
#define PINMUX_BALL_M17_GIOB_5 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_M17_SHIFT ) )

#define PINMUX_BALL_R3_EMIF_nRAS \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R3_SHIFT ) )
#define PINMUX_BALL_R3_GIOB_6 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R3_SHIFT ) )

#define PINMUX_BALL_P3_EMIF_nWAIT \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P3_SHIFT ) )
#define PINMUX_BALL_P3_GIOB_7 ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_P3_SHIFT ) )

#define PINMUX_BALL_D17_EMIF_nWE \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D17_SHIFT ) )
#define PINMUX_BALL_D17_EMIF_RNW \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D17_SHIFT ) )

#define PINMUX_BALL_E9_ETMDATA_08 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E9_SHIFT ) )
#define PINMUX_BALL_E9_EMIF_ADDR_05 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E9_SHIFT ) )

#define PINMUX_BALL_E8_ETMDATA_09 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E8_SHIFT ) )
#define PINMUX_BALL_E8_EMIF_ADDR_04 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E8_SHIFT ) )

#define PINMUX_BALL_E7_ETMDATA_10 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E7_SHIFT ) )
#define PINMUX_BALL_E7_EMIF_ADDR_03 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E7_SHIFT ) )

#define PINMUX_BALL_E6_ETMDATA_11 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E6_SHIFT ) )
#define PINMUX_BALL_E6_EMIF_ADDR_02 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E6_SHIFT ) )

#define PINMUX_BALL_E13_ETMDATA_12 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E13_SHIFT ) )
#define PINMUX_BALL_E13_EMIF_BA_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E13_SHIFT ) )

#define PINMUX_BALL_E12_ETMDATA_13 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E12_SHIFT ) )
#define PINMUX_BALL_E12_EMIF_nOE \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E12_SHIFT ) )

#define PINMUX_BALL_E11_ETMDATA_14 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E11_SHIFT ) )
#define PINMUX_BALL_E11_EMIF_nDQM_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E11_SHIFT ) )

#define PINMUX_BALL_E10_ETMDATA_15 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E10_SHIFT ) )
#define PINMUX_BALL_E10_EMIF_nDQM_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E10_SHIFT ) )

#define PINMUX_BALL_K15_ETMDATA_16 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K15_SHIFT ) )
#define PINMUX_BALL_K15_EMIF_DATA_00 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K15_SHIFT ) )

#define PINMUX_BALL_L15_ETMDATA_17 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_L15_SHIFT ) )
#define PINMUX_BALL_L15_EMIF_DATA_01 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_L15_SHIFT ) )

#define PINMUX_BALL_M15_ETMDATA_18 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_M15_SHIFT ) )
#define PINMUX_BALL_M15_EMIF_DATA_02 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_M15_SHIFT ) )

#define PINMUX_BALL_N15_ETMDATA_19 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N15_SHIFT ) )
#define PINMUX_BALL_N15_EMIF_DATA_03 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N15_SHIFT ) )

#define PINMUX_BALL_E5_ETMDATA_20 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E5_SHIFT ) )
#define PINMUX_BALL_E5_EMIF_DATA_04 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E5_SHIFT ) )

#define PINMUX_BALL_F5_ETMDATA_21 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_F5_SHIFT ) )
#define PINMUX_BALL_F5_EMIF_DATA_05 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_F5_SHIFT ) )

#define PINMUX_BALL_G5_ETMDATA_22 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G5_SHIFT ) )
#define PINMUX_BALL_G5_EMIF_DATA_06 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_G5_SHIFT ) )

#define PINMUX_BALL_K5_ETMDATA_23 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K5_SHIFT ) )
#define PINMUX_BALL_K5_EMIF_DATA_07 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K5_SHIFT ) )

#define PINMUX_BALL_L5_ETMDATA_24 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_L5_SHIFT ) )
#define PINMUX_BALL_L5_EMIF_DATA_08 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_L5_SHIFT ) )
#define PINMUX_BALL_L5_N2HET2_24 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_L5_SHIFT ) )
#define PINMUX_BALL_L5_MIBSPI5NCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_L5_SHIFT ) )

#define PINMUX_BALL_M5_ETMDATA_25 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_M5_SHIFT ) )
#define PINMUX_BALL_M5_EMIF_DATA_09 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_M5_SHIFT ) )
#define PINMUX_BALL_M5_N2HET2_25 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_M5_SHIFT ) )
#define PINMUX_BALL_M5_MIBSPI5NCS_5 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_M5_SHIFT ) )

#define PINMUX_BALL_N5_ETMDATA_26 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N5_SHIFT ) )
#define PINMUX_BALL_N5_EMIF_DATA_10 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N5_SHIFT ) )
#define PINMUX_BALL_N5_N2HET2_26 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_N5_SHIFT ) )

#define PINMUX_BALL_P5_ETMDATA_27 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P5_SHIFT ) )
#define PINMUX_BALL_P5_EMIF_DATA_11 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_P5_SHIFT ) )
#define PINMUX_BALL_P5_N2HET2_27 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_P5_SHIFT ) )

#define PINMUX_BALL_R5_ETMDATA_28 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R5_SHIFT ) )
#define PINMUX_BALL_R5_EMIF_DATA_12 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R5_SHIFT ) )
#define PINMUX_BALL_R5_N2HET2_28 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R5_SHIFT ) )
#define PINMUX_BALL_R5_GIOA_0 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R5_SHIFT ) )

#define PINMUX_BALL_R6_ETMDATA_29 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R6_SHIFT ) )
#define PINMUX_BALL_R6_EMIF_DATA_13 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R6_SHIFT ) )
#define PINMUX_BALL_R6_N2HET2_29 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R6_SHIFT ) )
#define PINMUX_BALL_R6_GIOA_1 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R6_SHIFT ) )

#define PINMUX_BALL_R7_ETMDATA_30 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R7_SHIFT ) )
#define PINMUX_BALL_R7_EMIF_DATA_14 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R7_SHIFT ) )
#define PINMUX_BALL_R7_N2HET2_30 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R7_SHIFT ) )
#define PINMUX_BALL_R7_GIOA_3 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R7_SHIFT ) )

#define PINMUX_BALL_R8_ETMDATA_31 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R8_SHIFT ) )
#define PINMUX_BALL_R8_EMIF_DATA_15 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R8_SHIFT ) )
#define PINMUX_BALL_R8_N2HET2_31 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R8_SHIFT ) )
#define PINMUX_BALL_R8_GIOA_4 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R8_SHIFT ) )

#define PINMUX_BALL_R9_ETMTRACECLKIN \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R9_SHIFT ) )
#define PINMUX_BALL_R9_EXTCLKIN2 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R9_SHIFT ) )
#define PINMUX_BALL_R9_GIOA_5 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R9_SHIFT ) )

#define PINMUX_BALL_R10_ETMTRACECLKOUT \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R10_SHIFT ) )
#define PINMUX_BALL_R10_GIOA_6 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R10_SHIFT ) )

#define PINMUX_BALL_R11_ETMTRACECTL \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R11_SHIFT ) )
#define PINMUX_BALL_R11_GIOA_7 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_R11_SHIFT ) )

#define PINMUX_BALL_B15_FRAYTX1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B15_SHIFT ) )
#define PINMUX_BALL_B15_GIOA_2 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B15_SHIFT ) )

#define PINMUX_BALL_B8_FRAYTX2 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B8_SHIFT ) )
#define PINMUX_BALL_B8_GIOB_0  ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B8_SHIFT ) )

#define PINMUX_BALL_B16_FRAYTXEN1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B16_SHIFT ) )
#define PINMUX_BALL_B16_GIOB_1 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B16_SHIFT ) )

#define PINMUX_BALL_B9_FRAYTXEN2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B9_SHIFT ) )
#define PINMUX_BALL_B9_GIOB_2 ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B9_SHIFT ) )

#define PINMUX_BALL_C1_GIOA_2 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C1_N2HET2_00 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_C1_SHIFT ) )
#define PINMUX_BALL_C1_eQEP2I ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_C1_SHIFT ) )

#define PINMUX_BALL_E1_GIOA_3 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E1_SHIFT ) )
#define PINMUX_BALL_E1_N2HET2_02 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_E1_SHIFT ) )

#define PINMUX_BALL_B5_GIOA_5   ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B5_SHIFT ) )
#define PINMUX_BALL_B5_EXTCLKIN ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B5_SHIFT ) )
#define PINMUX_BALL_B5_eTPWM1A  ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_B5_SHIFT ) )

#define PINMUX_BALL_H3_GIOA_6   ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H3_SHIFT ) )
#define PINMUX_BALL_H3_N2HET2_04 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_H3_SHIFT ) )
#define PINMUX_BALL_H3_eTPWM1B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_H3_SHIFT ) )

#define PINMUX_BALL_M1_GIOA_7  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_M1_SHIFT ) )
#define PINMUX_BALL_M1_N2HET2_06 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_M1_SHIFT ) )
#define PINMUX_BALL_M1_eTPWM2A ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_M1_SHIFT ) )

#define PINMUX_BALL_F2_GIOB_2  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_F2_SHIFT ) )
#define PINMUX_BALL_F2_DCAN4TX ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_F2_SHIFT ) )

#define PINMUX_BALL_W10_GIOB_3 ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W10_SHIFT ) )
#define PINMUX_BALL_W10_DCAN4RX \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_W10_SHIFT ) )

#define PINMUX_BALL_J2_GIOB_6  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J2_SHIFT ) )
#define PINMUX_BALL_J2_nERROR1 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J2_SHIFT ) )

#define PINMUX_BALL_F1_GIOB_7  ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_F1_SHIFT ) )
#define PINMUX_BALL_F1_nERROR2 ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_F1_SHIFT ) )
#define PINMUX_BALL_F1_nTZ1_2  ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_F1_SHIFT ) )

#define PINMUX_BALL_R2_MIBSPI1NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_MIBSPI1SOMI_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_MII_TXD_2 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_R2_SHIFT ) )
#define PINMUX_BALL_R2_ECAP6 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_R2_SHIFT ) )

#define PINMUX_BALL_F3_MIBSPI1NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_MII_COL ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_N2HET1_17 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_F3_SHIFT ) )
#define PINMUX_BALL_F3_eQEP1S ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_F3_SHIFT ) )

#define PINMUX_BALL_G3_MIBSPI1NCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G3_SHIFT ) )
#define PINMUX_BALL_G3_MDIO ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_G3_SHIFT ) )
#define PINMUX_BALL_G3_N2HET1_19 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_G3_SHIFT ) )

#define PINMUX_BALL_J3_MIBSPI1NCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J3_SHIFT ) )
#define PINMUX_BALL_J3_N2HET1_21 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_J3_SHIFT ) )
#define PINMUX_BALL_J3_nTZ1_3 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_J3_SHIFT ) )

#define PINMUX_BALL_G19_MIBSPI1NENA \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_MII_RXD_2 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_N2HET1_23 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_G19_SHIFT ) )
#define PINMUX_BALL_G19_ECAP4 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_G19_SHIFT ) )

#define PINMUX_BALL_V9_MIBSPI3CLK \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V9_SHIFT ) )
#define PINMUX_BALL_V9_EXT_SEL_01 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V9_SHIFT ) )
#define PINMUX_BALL_V9_eQEP1A ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V9_SHIFT ) )

#define PINMUX_BALL_V10_MIBSPI3NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_V10_AD2EVT ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V10_SHIFT ) )
#define PINMUX_BALL_V10_eQEP1I \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V10_SHIFT ) )

#define PINMUX_BALL_V5_MIBSPI3NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V5_SHIFT ) )
#define PINMUX_BALL_V5_MDCLK ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_V5_SHIFT ) )
#define PINMUX_BALL_V5_N2HET1_25 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V5_SHIFT ) )

#define PINMUX_BALL_B2_MIBSPI3NCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B2_I2C1_SDA ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B2_N2HET1_27 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B2_SHIFT ) )
#define PINMUX_BALL_B2_nTZ1_2 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_B2_SHIFT ) )

#define PINMUX_BALL_C3_MIBSPI3NCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C3_I2C1_SCL ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C3_N2HET1_29 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_C3_SHIFT ) )
#define PINMUX_BALL_C3_nTZ1_1 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_C3_SHIFT ) )

#define PINMUX_BALL_W9_MIBSPI3NENA \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W9_MIBSPI3NCS_5 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W9_N2HET1_31 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_W9_SHIFT ) )
#define PINMUX_BALL_W9_eQEP1B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_W9_SHIFT ) )

#define PINMUX_BALL_W8_MIBSPI3SIMO \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W8_SHIFT ) )
#define PINMUX_BALL_W8_EXT_SEL_00 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W8_SHIFT ) )
#define PINMUX_BALL_W8_ECAP3 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_W8_SHIFT ) )

#define PINMUX_BALL_V8_MIBSPI3SOMI \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V8_SHIFT ) )
#define PINMUX_BALL_V8_EXT_ENA ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V8_SHIFT ) )
#define PINMUX_BALL_V8_ECAP2   ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V8_SHIFT ) )

#define PINMUX_BALL_H19_MIBSPI5CLK \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_H19_DMM_DATA_04 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_H19_MII_TXEN \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_H19_SHIFT ) )
#define PINMUX_BALL_H19_RMII_TXEN \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_H19_SHIFT ) )

#define PINMUX_BALL_E19_MIBSPI5NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E19_SHIFT ) )
#define PINMUX_BALL_E19_DMM_DATA_05 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E19_SHIFT ) )
#define PINMUX_BALL_E19_eTPWM4A \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_E19_SHIFT ) )

#define PINMUX_BALL_B6_MIBSPI5NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B6_SHIFT ) )
#define PINMUX_BALL_B6_DMM_DATA_06 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B6_SHIFT ) )

#define PINMUX_BALL_W6_MIBSPI5NCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W6_SHIFT ) )
#define PINMUX_BALL_W6_DMM_DATA_02 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W6_SHIFT ) )

#define PINMUX_BALL_T12_MIBSPI5NCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_T12_SHIFT ) )
#define PINMUX_BALL_T12_DMM_DATA_03 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_T12_SHIFT ) )

#define PINMUX_BALL_H18_MIBSPI5NENA \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_DMM_DATA_07 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_MII_RXD_3 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_H18_SHIFT ) )
#define PINMUX_BALL_H18_ECAP5 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_H18_SHIFT ) )

#define PINMUX_BALL_J19_MIBSPI5SIMO_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_J19_DMM_DATA_08 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_J19_MII_TXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_J19_SHIFT ) )
#define PINMUX_BALL_J19_RMII_TXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_J19_SHIFT ) )

#define PINMUX_BALL_E16_MIBSPI5SIMO_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E16_SHIFT ) )
#define PINMUX_BALL_E16_DMM_DATA_09 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E16_SHIFT ) )
#define PINMUX_BALL_E16_EXT_SEL_00 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_E16_SHIFT ) )

#define PINMUX_BALL_H17_MIBSPI5SIMO_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H17_SHIFT ) )
#define PINMUX_BALL_H17_DMM_DATA_10 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_H17_SHIFT ) )
#define PINMUX_BALL_H17_EXT_SEL_01 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_H17_SHIFT ) )

#define PINMUX_BALL_G17_MIBSPI5SIMO_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G17_SHIFT ) )
#define PINMUX_BALL_G17_DMM_DATA_11 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_G17_SHIFT ) )
#define PINMUX_BALL_G17_I2C2_SDA \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_G17_SHIFT ) )
#define PINMUX_BALL_G17_EXT_SEL_02 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_G17_SHIFT ) )

#define PINMUX_BALL_J18_MIBSPI5SOMI_0 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_J18_DMM_DATA_12 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_J18_MII_TXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_J18_SHIFT ) )
#define PINMUX_BALL_J18_RMII_TXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_J18_SHIFT ) )

#define PINMUX_BALL_E17_MIBSPI5SOMI_1 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E17_SHIFT ) )
#define PINMUX_BALL_E17_DMM_DATA_13 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E17_SHIFT ) )
#define PINMUX_BALL_E17_EXT_SEL_03 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_E17_SHIFT ) )

#define PINMUX_BALL_H16_MIBSPI5SOMI_2 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H16_SHIFT ) )
#define PINMUX_BALL_H16_DMM_DATA_14 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_H16_SHIFT ) )
#define PINMUX_BALL_H16_EXT_SEL_04 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_H16_SHIFT ) )

#define PINMUX_BALL_G16_MIBSPI5SOMI_3 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_G16_SHIFT ) )
#define PINMUX_BALL_G16_DMM_DATA_15 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_G16_SHIFT ) )
#define PINMUX_BALL_G16_I2C2_SCL \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_G16_SHIFT ) )
#define PINMUX_BALL_G16_EXT_ENA \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_G16_SHIFT ) )

#define PINMUX_BALL_K18_N2HET1_00 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K18_SHIFT ) )
#define PINMUX_BALL_K18_MIBSPI4CLK \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_K18_SHIFT ) )
#define PINMUX_BALL_K18_eTPWM2B \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_K18_SHIFT ) )

#define PINMUX_BALL_V2_N2HET1_01 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_MIBSPI4NENA \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_N2HET2_08 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V2_SHIFT ) )
#define PINMUX_BALL_V2_eQEP2A ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V2_SHIFT ) )

#define PINMUX_BALL_W5_N2HET1_02 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W5_SHIFT ) )
#define PINMUX_BALL_W5_MIBSPI4SIMO \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W5_SHIFT ) )
#define PINMUX_BALL_W5_eTPWM3A ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_W5_SHIFT ) )

#define PINMUX_BALL_U1_N2HET1_03 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_MIBSPI4NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_N2HET2_10 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_U1_SHIFT ) )
#define PINMUX_BALL_U1_eQEP2B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_U1_SHIFT ) )

#define PINMUX_BALL_B12_N2HET1_04 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B12_SHIFT ) )
#define PINMUX_BALL_B12_MIBSPI4NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B12_SHIFT ) )
#define PINMUX_BALL_B12_eTPWM4B \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_B12_SHIFT ) )

#define PINMUX_BALL_V6_N2HET1_05 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V6_MIBSPI4SOMI \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V6_N2HET2_12 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V6_SHIFT ) )
#define PINMUX_BALL_V6_eTPWM3B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V6_SHIFT ) )

#define PINMUX_BALL_W3_N2HET1_06 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_W3_SHIFT ) )
#define PINMUX_BALL_W3_SCI3RX  ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_W3_SHIFT ) )
#define PINMUX_BALL_W3_eTPWM5A ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_W3_SHIFT ) )

#define PINMUX_BALL_T1_N2HET1_07 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_MIBSPI4NCS_2 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_N2HET2_14 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_T1_SHIFT ) )
#define PINMUX_BALL_T1_eTPWM7B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_T1_SHIFT ) )

#define PINMUX_BALL_E18_N2HET1_08 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_E18_MIBSPI1SIMO_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E18_SHIFT ) )
#define PINMUX_BALL_E18_MII_TXD_3 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_E18_SHIFT ) )

#define PINMUX_BALL_V7_N2HET1_09 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_MIBSPI4NCS_3 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_N2HET2_16 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_V7_SHIFT ) )
#define PINMUX_BALL_V7_eTPWM7A ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_V7_SHIFT ) )

#define PINMUX_BALL_D19_N2HET1_10 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_MIBSPI4NCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_MII_TX_CLK \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_MII_TX_AVCLK4 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_D19_SHIFT ) )
#define PINMUX_BALL_D19_nTZ1_3 \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_D19_SHIFT ) )

#define PINMUX_BALL_E3_N2HET1_11 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_MIBSPI3NCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_N2HET2_18 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_E3_SHIFT ) )
#define PINMUX_BALL_E3_ETPWM1SYNCO \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_E3_SHIFT ) )

#define PINMUX_BALL_B4_N2HET1_12 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_B4_MIBSPI4NCS_5 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_B4_MII_CRS ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B4_SHIFT ) )
#define PINMUX_BALL_B4_RMII_CRS_DV \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_B4_SHIFT ) )

#define PINMUX_BALL_N2_N2HET1_13 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N2_SCI3TX ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N2_N2HET2_20 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_N2_SHIFT ) )
#define PINMUX_BALL_N2_eTPWM5B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_N2_SHIFT ) )

#define PINMUX_BALL_N1_N2HET1_15 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_N1_MIBSPI1NCS_4 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_N1_N2HET2_22 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_N1_SHIFT ) )
#define PINMUX_BALL_N1_ECAP1 ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_N1_SHIFT ) )

#define PINMUX_BALL_A4_N2HET1_16 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A4_SHIFT ) )
#define PINMUX_BALL_A4_ETPWM1SYNCI \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_A4_SHIFT ) )
#define PINMUX_BALL_A4_ETPWM1SYNCO \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_A4_SHIFT ) )

#define PINMUX_BALL_A13_N2HET1_17 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A13_SHIFT ) )
#define PINMUX_BALL_A13_EMIF_nOE \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_A13_SHIFT ) )
#define PINMUX_BALL_A13_SCI4RX ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_A13_SHIFT ) )

#define PINMUX_BALL_J1_N2HET1_18 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J1_SHIFT ) )
#define PINMUX_BALL_J1_EMIF_RNW ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J1_SHIFT ) )
#define PINMUX_BALL_J1_eTPWM6A  ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_J1_SHIFT ) )

#define PINMUX_BALL_B13_N2HET1_19 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B13_SHIFT ) )
#define PINMUX_BALL_B13_EMIF_nDQM_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B13_SHIFT ) )
#define PINMUX_BALL_B13_SCI4TX ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B13_SHIFT ) )

#define PINMUX_BALL_P2_N2HET1_20 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P2_SHIFT ) )
#define PINMUX_BALL_P2_EMIF_nDQM_1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_P2_SHIFT ) )
#define PINMUX_BALL_P2_eTPWM6B ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_P2_SHIFT ) )

#define PINMUX_BALL_H4_N2HET1_21 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_H4_SHIFT ) )
#define PINMUX_BALL_H4_EMIF_nDQM_2 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_H4_SHIFT ) )

#define PINMUX_BALL_B3_N2HET1_22 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B3_SHIFT ) )
#define PINMUX_BALL_B3_EMIF_nDQM_3 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_B3_SHIFT ) )

#define PINMUX_BALL_J4_N2HET1_23 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_J4_SHIFT ) )
#define PINMUX_BALL_J4_EMIF_BA_0 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_J4_SHIFT ) )

#define PINMUX_BALL_P1_N2HET1_24 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P1_MIBSPI1NCS_5 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P1_MII_RXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_P1_SHIFT ) )
#define PINMUX_BALL_P1_RMII_RXD_0 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_P1_SHIFT ) )

#define PINMUX_BALL_A14_N2HET1_26 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_A14_SHIFT ) )
#define PINMUX_BALL_A14_MII_RXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_A14_SHIFT ) )
#define PINMUX_BALL_A14_RMII_RXD_1 \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_A14_SHIFT ) )

#define PINMUX_BALL_K19_N2HET1_28 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_K19_MII_RXCLK \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_K19_RMII_REFCLK \
    ( ( uint32 ) ( ( uint32 ) 0x8U << PINMUX_BALL_K19_SHIFT ) )
#define PINMUX_BALL_K19_MII_RX_AVCLK4 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_K19_SHIFT ) )

#define PINMUX_BALL_B11_N2HET1_30 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_B11_MII_RX_DV \
    ( ( uint32 ) ( ( uint32 ) 0x4U << PINMUX_BALL_B11_SHIFT ) )
#define PINMUX_BALL_B11_eQEP2S \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_B11_SHIFT ) )

#define PINMUX_BALL_D8_N2HET2_01 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D8_SHIFT ) )
#define PINMUX_BALL_D8_N2HET1_NDIS \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D8_SHIFT ) )

#define PINMUX_BALL_D7_N2HET2_02 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D7_SHIFT ) )
#define PINMUX_BALL_D7_N2HET2_NDIS \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_D7_SHIFT ) )

#define PINMUX_BALL_D3_N2HET2_12 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D3_SHIFT ) )
#define PINMUX_BALL_D3_MIBSPI2NENA \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_D3_SHIFT ) )
#define PINMUX_BALL_D3_MIBSPI2NCS_1 \
    ( ( uint32 ) ( ( uint32 ) 0x20U << PINMUX_BALL_D3_SHIFT ) )

#define PINMUX_BALL_D2_N2HET2_13 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D2_SHIFT ) )
#define PINMUX_BALL_D2_MIBSPI2SOMI \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_D2_SHIFT ) )

#define PINMUX_BALL_D1_N2HET2_14 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_D1_SHIFT ) )
#define PINMUX_BALL_D1_MIBSPI2SIMO \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_D1_SHIFT ) )

#define PINMUX_BALL_P4_N2HET2_19 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_P4_SHIFT ) )
#define PINMUX_BALL_P4_LIN2RX ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_P4_SHIFT ) )

#define PINMUX_BALL_T5_N2HET2_20 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_T5_SHIFT ) )
#define PINMUX_BALL_T5_LIN2TX ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_BALL_T5_SHIFT ) )

#define PINMUX_BALL_T4_MII_RXCLK \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_T4_SHIFT ) )
#define PINMUX_BALL_T4_MII_RX_AVCLK4 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_T4_SHIFT ) )

#define PINMUX_BALL_U7_MII_TX_CLK \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_U7_SHIFT ) )
#define PINMUX_BALL_U7_MII_TX_AVCLK4 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_U7_SHIFT ) )

#define PINMUX_BALL_E2_N2HET2_03 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_E2_SHIFT ) )
#define PINMUX_BALL_E2_MIBSPI2CLK \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_E2_SHIFT ) )

#define PINMUX_BALL_N3_N2HET2_07 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_BALL_N3_SHIFT ) )
#define PINMUX_BALL_N3_MIBSPI2NCS_0 \
    ( ( uint32 ) ( ( uint32 ) 0x10U << PINMUX_BALL_N3_SHIFT ) )

#define PINMUX_GATE_EMIF_CLK_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_GATE_EMIF_CLK_SHIFT ) )
#define PINMUX_EMIF_OUTPUT_ENABLE_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EMIF_OUTPUT_ENABLE_SHIFT ) )
#define PINMUX_GIOA_DISABLE_HET1_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_GIOA_DISABLE_HET1_SHIFT ) )
#define PINMUX_GIOB_DISABLE_HET2_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_GIOB_DISABLE_HET2_SHIFT ) )
#define PINMUX_GATE_EMIF_CLK_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GATE_EMIF_CLK_SHIFT ) )
#define PINMUX_EMIF_OUTPUT_ENABLE_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_EMIF_OUTPUT_ENABLE_SHIFT ) )
#define PINMUX_GIOA_DISABLE_HET1_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA_DISABLE_HET1_SHIFT ) )
#define PINMUX_GIOB_DISABLE_HET2_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB_DISABLE_HET2_SHIFT ) )
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
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_TIME_BASE_SYNC_SHIFT ) )
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
#define PINMUX_ETPWM_SOC1A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC1A_SHIFT ) )
#define PINMUX_ETPWM_SOC1A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC1A_SHIFT ) )
#define PINMUX_ETPWM_SOC2A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC2A_SHIFT ) )
#define PINMUX_ETPWM_SOC2A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC2A_SHIFT ) )
#define PINMUX_ETPWM_SOC3A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC3A_SHIFT ) )
#define PINMUX_ETPWM_SOC3A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC3A_SHIFT ) )
#define PINMUX_ETPWM_SOC4A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC4A_SHIFT ) )
#define PINMUX_ETPWM_SOC4A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC4A_SHIFT ) )
#define PINMUX_ETPWM_SOC5A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC5A_SHIFT ) )
#define PINMUX_ETPWM_SOC5A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC5A_SHIFT ) )
#define PINMUX_ETPWM_SOC6A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC6A_SHIFT ) )
#define PINMUX_ETPWM_SOC6A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC6A_SHIFT ) )
#define PINMUX_ETPWM_SOC7A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC7A_SHIFT ) )
#define PINMUX_ETPWM_SOC7A_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ETPWM_SOC7A_SHIFT ) )
#define PINMUX_ETPWM_SOC1A_ON \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_ETPWM_SOC1A_SHIFT ) )
#define PINMUX_EQEP1A_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP1A_FILTER_SHIFT ) )
#define PINMUX_EQEP1A_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP1A_FILTER_SHIFT ) )
#define PINMUX_EQEP1B_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP1B_FILTER_SHIFT ) )
#define PINMUX_EQEP1B_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP1B_FILTER_SHIFT ) )
#define PINMUX_EQEP1I_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP1I_FILTER_SHIFT ) )
#define PINMUX_EQEP1I_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP1I_FILTER_SHIFT ) )
#define PINMUX_EQEP1S_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP1S_FILTER_SHIFT ) )
#define PINMUX_EQEP1S_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP1S_FILTER_SHIFT ) )
#define PINMUX_EQEP2A_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP2A_FILTER_SHIFT ) )
#define PINMUX_EQEP2A_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP2A_FILTER_SHIFT ) )
#define PINMUX_EQEP2B_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP2B_FILTER_SHIFT ) )
#define PINMUX_EQEP2B_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP2B_FILTER_SHIFT ) )
#define PINMUX_EQEP2I_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP2I_FILTER_SHIFT ) )
#define PINMUX_EQEP2I_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP2I_FILTER_SHIFT ) )
#define PINMUX_EQEP2S_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_EQEP2S_FILTER_SHIFT ) )
#define PINMUX_EQEP2S_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_EQEP2S_FILTER_SHIFT ) )

#define PINMUX_ECAP1_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ECAP1_FILTER_SHIFT ) )
#define PINMUX_ECAP1_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ECAP1_FILTER_SHIFT ) )
#define PINMUX_ECAP2_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ECAP2_FILTER_SHIFT ) )
#define PINMUX_ECAP2_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ECAP2_FILTER_SHIFT ) )
#define PINMUX_ECAP3_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ECAP3_FILTER_SHIFT ) )
#define PINMUX_ECAP3_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ECAP3_FILTER_SHIFT ) )
#define PINMUX_ECAP4_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ECAP4_FILTER_SHIFT ) )
#define PINMUX_ECAP4_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ECAP4_FILTER_SHIFT ) )
#define PINMUX_ECAP5_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ECAP5_FILTER_SHIFT ) )
#define PINMUX_ECAP5_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ECAP5_FILTER_SHIFT ) )
#define PINMUX_ECAP6_FILTER_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_ECAP6_FILTER_SHIFT ) )
#define PINMUX_ECAP6_FILTER_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_ECAP6_FILTER_SHIFT ) )

#define PINMUX_GIOA0_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA0_DMA_SHIFT ) )
#define PINMUX_GIOA0_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA0_DMA_SHIFT ) )
#define PINMUX_GIOA1_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA1_DMA_SHIFT ) )
#define PINMUX_GIOA1_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA1_DMA_SHIFT ) )
#define PINMUX_GIOA2_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA2_DMA_SHIFT ) )
#define PINMUX_GIOA2_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA2_DMA_SHIFT ) )
#define PINMUX_GIOA3_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA3_DMA_SHIFT ) )
#define PINMUX_GIOA3_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA3_DMA_SHIFT ) )
#define PINMUX_GIOA4_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA4_DMA_SHIFT ) )
#define PINMUX_GIOA4_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA4_DMA_SHIFT ) )
#define PINMUX_GIOA5_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA5_DMA_SHIFT ) )
#define PINMUX_GIOA5_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA5_DMA_SHIFT ) )
#define PINMUX_GIOA6_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA6_DMA_SHIFT ) )
#define PINMUX_GIOA6_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA6_DMA_SHIFT ) )
#define PINMUX_GIOA7_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOA7_DMA_SHIFT ) )
#define PINMUX_GIOA7_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOA7_DMA_SHIFT ) )
#define PINMUX_GIOB0_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB0_DMA_SHIFT ) )
#define PINMUX_GIOB0_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB0_DMA_SHIFT ) )
#define PINMUX_GIOB1_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB1_DMA_SHIFT ) )
#define PINMUX_GIOB1_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB1_DMA_SHIFT ) )
#define PINMUX_GIOB2_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB2_DMA_SHIFT ) )
#define PINMUX_GIOB2_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB2_DMA_SHIFT ) )
#define PINMUX_GIOB3_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB3_DMA_SHIFT ) )
#define PINMUX_GIOB3_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB3_DMA_SHIFT ) )
#define PINMUX_GIOB4_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB4_DMA_SHIFT ) )
#define PINMUX_GIOB4_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB4_DMA_SHIFT ) )
#define PINMUX_GIOB5_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB5_DMA_SHIFT ) )
#define PINMUX_GIOB5_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB5_DMA_SHIFT ) )
#define PINMUX_GIOB6_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB6_DMA_SHIFT ) )
#define PINMUX_GIOB6_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB6_DMA_SHIFT ) )
#define PINMUX_GIOB7_DMA_ON  ( ( uint32 ) ( ( uint32 ) 0x0U << PINMUX_GIOB7_DMA_SHIFT ) )
#define PINMUX_GIOB7_DMA_OFF ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_GIOB7_DMA_SHIFT ) )
#define PINMUX_TEMP1_ENABLE_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_TEMP1_ENABLE_SHIFT ) )
#define PINMUX_TEMP1_ENABLE_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_TEMP1_ENABLE_SHIFT ) )
#define PINMUX_TEMP2_ENABLE_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_TEMP2_ENABLE_SHIFT ) )
#define PINMUX_TEMP2_ENABLE_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_TEMP2_ENABLE_SHIFT ) )
#define PINMUX_TEMP3_ENABLE_ON \
    ( ( uint32 ) ( ( uint32 ) 0x2U << PINMUX_TEMP3_ENABLE_SHIFT ) )
#define PINMUX_TEMP3_ENABLE_OFF \
    ( ( uint32 ) ( ( uint32 ) 0x1U << PINMUX_TEMP3_ENABLE_SHIFT ) )

#define SIGNAL_AD2EVT_SHIFT       0U
#define SIGNAL_GIOA_0_SHIFT       24U
#define SIGNAL_GIOA_1_SHIFT       0U
#define SIGNAL_GIOA_2_SHIFT       8U
#define SIGNAL_GIOA_3_SHIFT       16U
#define SIGNAL_GIOA_4_SHIFT       24U
#define SIGNAL_GIOA_5_SHIFT       0U
#define SIGNAL_GIOA_6_SHIFT       8U
#define SIGNAL_GIOA_7_SHIFT       16U
#define SIGNAL_GIOB_0_SHIFT       24U
#define SIGNAL_GIOB_1_SHIFT       0U
#define SIGNAL_GIOB_2_SHIFT       8U
#define SIGNAL_GIOB_3_SHIFT       16U
#define SIGNAL_GIOB_4_SHIFT       24U
#define SIGNAL_GIOB_5_SHIFT       0U
#define SIGNAL_GIOB_6_SHIFT       8U
#define SIGNAL_GIOB_7_SHIFT       16U
#define SIGNAL_MDIO_SHIFT         24U
#define SIGNAL_MIBSPI1NCS_4_SHIFT 0U
#define SIGNAL_MIBSPI1NCS_5_SHIFT 8U
#define SIGNAL_MII_COL_SHIFT      16U
#define SIGNAL_MII_CRS_SHIFT      24U
#define SIGNAL_MII_RX_DV_SHIFT    0U
#define SIGNAL_MII_RX_ER_SHIFT    8U
#define SIGNAL_MII_RXCLK_SHIFT    16U
#define SIGNAL_MII_RXD_0_SHIFT    24U
#define SIGNAL_MII_RXD_1_SHIFT    0U
#define SIGNAL_MII_RXD_2_SHIFT    8U
#define SIGNAL_MII_RXD_3_SHIFT    16U
#define SIGNAL_MII_TX_CLK_SHIFT   24U
#define SIGNAL_N2HET1_17_SHIFT    0U
#define SIGNAL_N2HET1_19_SHIFT    8U
#define SIGNAL_N2HET1_21_SHIFT    16U
#define SIGNAL_N2HET1_23_SHIFT    24U
#define SIGNAL_N2HET1_25_SHIFT    0U
#define SIGNAL_N2HET1_27_SHIFT    8U
#define SIGNAL_N2HET1_29_SHIFT    16U
#define SIGNAL_N2HET1_31_SHIFT    24U
#define SIGNAL_N2HET2_00_SHIFT    0U
#define SIGNAL_N2HET2_01_SHIFT    8U
#define SIGNAL_N2HET2_02_SHIFT    16U
#define SIGNAL_N2HET2_03_SHIFT    24U
#define SIGNAL_N2HET2_04_SHIFT    0U
#define SIGNAL_N2HET2_05_SHIFT    8U
#define SIGNAL_N2HET2_06_SHIFT    16U
#define SIGNAL_N2HET2_07_SHIFT    24U
#define SIGNAL_N2HET2_08_SHIFT    0U
#define SIGNAL_N2HET2_09_SHIFT    8U
#define SIGNAL_N2HET2_10_SHIFT    16U
#define SIGNAL_N2HET2_11_SHIFT    24U
#define SIGNAL_N2HET2_12_SHIFT    0U
#define SIGNAL_N2HET2_13_SHIFT    8U
#define SIGNAL_N2HET2_14_SHIFT    16U
#define SIGNAL_N2HET2_15_SHIFT    24U
#define SIGNAL_N2HET2_16_SHIFT    0U
#define SIGNAL_N2HET2_18_SHIFT    8U
#define SIGNAL_N2HET2_20_SHIFT    16U
#define SIGNAL_N2HET2_22_SHIFT    24U
#define SIGNAL_nTZ1_1_SHIFT       0U
#define SIGNAL_nTZ1_2_SHIFT       8U
#define SIGNAL_nTZ1_3_SHIFT       16U

#define SIGNAL_AD2EVT_T10         ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_AD2EVT_SHIFT ) )
#define SIGNAL_AD2EVT_V10         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_AD2EVT_SHIFT ) )

#define SIGNAL_GIOA_0_A5          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_0_SHIFT ) )
#define SIGNAL_GIOA_0_R5          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_0_SHIFT ) )

#define SIGNAL_GIOA_1_C2          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_1_SHIFT ) )
#define SIGNAL_GIOA_1_R6          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_1_SHIFT ) )

#define SIGNAL_GIOA_2_C1          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_2_SHIFT ) )
#define SIGNAL_GIOA_2_B15         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_2_SHIFT ) )

#define SIGNAL_GIOA_3_E1          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_3_SHIFT ) )
#define SIGNAL_GIOA_3_R7          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_3_SHIFT ) )

#define SIGNAL_GIOA_4_A6          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_4_SHIFT ) )
#define SIGNAL_GIOA_4_R8          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_4_SHIFT ) )

#define SIGNAL_GIOA_5_B5          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_5_SHIFT ) )
#define SIGNAL_GIOA_5_R9          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_5_SHIFT ) )

#define SIGNAL_GIOA_6_H3          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_6_SHIFT ) )
#define SIGNAL_GIOA_6_R10         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_6_SHIFT ) )

#define SIGNAL_GIOA_7_M1          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOA_7_SHIFT ) )
#define SIGNAL_GIOA_7_R11         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOA_7_SHIFT ) )

#define SIGNAL_GIOB_0_M2          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_0_SHIFT ) )
#define SIGNAL_GIOB_0_B8          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_0_SHIFT ) )

#define SIGNAL_GIOB_1_K2          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_1_SHIFT ) )
#define SIGNAL_GIOB_1_B16         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_1_SHIFT ) )

#define SIGNAL_GIOB_2_F2          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_2_SHIFT ) )
#define SIGNAL_GIOB_2_B9          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_2_SHIFT ) )

#define SIGNAL_GIOB_3_W10         ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_3_SHIFT ) )
#define SIGNAL_GIOB_3_R4          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_3_SHIFT ) )

#define SIGNAL_GIOB_4_G1          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_4_SHIFT ) )
#define SIGNAL_GIOB_4_L17         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_4_SHIFT ) )

#define SIGNAL_GIOB_5_G2          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_5_SHIFT ) )
#define SIGNAL_GIOB_5_M17         ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_5_SHIFT ) )

#define SIGNAL_GIOB_6_J2          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_6_SHIFT ) )
#define SIGNAL_GIOB_6_R3          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_6_SHIFT ) )

#define SIGNAL_GIOB_7_F1          ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_GIOB_7_SHIFT ) )
#define SIGNAL_GIOB_7_P3          ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_GIOB_7_SHIFT ) )

#define SIGNAL_MDIO_F4            ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MDIO_SHIFT ) )
#define SIGNAL_MDIO_G3            ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MDIO_SHIFT ) )

#define SIGNAL_MIBSPI1NCS_4_U10 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MIBSPI1NCS_4_SHIFT ) )
#define SIGNAL_MIBSPI1NCS_4_N1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MIBSPI1NCS_4_SHIFT ) )

#define SIGNAL_MIBSPI1NCS_5_U9 \
    ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MIBSPI1NCS_5_SHIFT ) )
#define SIGNAL_MIBSPI1NCS_5_P1 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MIBSPI1NCS_5_SHIFT ) )

#define SIGNAL_MII_COL_W4    ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_COL_SHIFT ) )
#define SIGNAL_MII_COL_F3    ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_COL_SHIFT ) )

#define SIGNAL_MII_CRS_V4    ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_CRS_SHIFT ) )
#define SIGNAL_MII_CRS_B4    ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_CRS_SHIFT ) )

#define SIGNAL_MII_RX_DV_U6  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RX_DV_SHIFT ) )
#define SIGNAL_MII_RX_DV_B11 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RX_DV_SHIFT ) )

#define SIGNAL_MII_RX_ER_U5  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RX_ER_SHIFT ) )
#define SIGNAL_MII_RX_ER_N19 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RX_ER_SHIFT ) )

#define SIGNAL_MII_RXCLK_T4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RXCLK_SHIFT ) )
#define SIGNAL_MII_RXCLK_K19 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RXCLK_SHIFT ) )

#define SIGNAL_MII_RXD_0_U4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RXD_0_SHIFT ) )
#define SIGNAL_MII_RXD_0_P1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RXD_0_SHIFT ) )

#define SIGNAL_MII_RXD_1_T3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RXD_1_SHIFT ) )
#define SIGNAL_MII_RXD_1_A14 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RXD_1_SHIFT ) )

#define SIGNAL_MII_RXD_2_U3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RXD_2_SHIFT ) )
#define SIGNAL_MII_RXD_2_G19 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RXD_2_SHIFT ) )

#define SIGNAL_MII_RXD_3_V3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_RXD_3_SHIFT ) )
#define SIGNAL_MII_RXD_3_H18 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_RXD_3_SHIFT ) )

#define SIGNAL_MII_TX_CLK_U7 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_MII_TX_CLK_SHIFT ) )
#define SIGNAL_MII_TX_CLK_D19 \
    ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_MII_TX_CLK_SHIFT ) )

#define SIGNAL_N2HET1_17_A13 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_17_SHIFT ) )
#define SIGNAL_N2HET1_17_F3  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_17_SHIFT ) )

#define SIGNAL_N2HET1_19_B13 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_19_SHIFT ) )
#define SIGNAL_N2HET1_19_G3  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_19_SHIFT ) )

#define SIGNAL_N2HET1_21_H4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_21_SHIFT ) )
#define SIGNAL_N2HET1_21_J3  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_21_SHIFT ) )

#define SIGNAL_N2HET1_23_J4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_23_SHIFT ) )
#define SIGNAL_N2HET1_23_G19 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_23_SHIFT ) )

#define SIGNAL_N2HET1_25_M3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_25_SHIFT ) )
#define SIGNAL_N2HET1_25_V5  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_25_SHIFT ) )

#define SIGNAL_N2HET1_27_A9  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_27_SHIFT ) )
#define SIGNAL_N2HET1_27_B2  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_27_SHIFT ) )

#define SIGNAL_N2HET1_29_A3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_29_SHIFT ) )
#define SIGNAL_N2HET1_29_C3  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_29_SHIFT ) )

#define SIGNAL_N2HET1_31_J17 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET1_31_SHIFT ) )
#define SIGNAL_N2HET1_31_W9  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET1_31_SHIFT ) )

#define SIGNAL_N2HET2_00_D6  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_00_SHIFT ) )
#define SIGNAL_N2HET2_00_C1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_00_SHIFT ) )

#define SIGNAL_N2HET2_01_D8  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_01_SHIFT ) )
#define SIGNAL_N2HET2_01_D4  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_01_SHIFT ) )

#define SIGNAL_N2HET2_02_D7  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_02_SHIFT ) )
#define SIGNAL_N2HET2_02_E1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_02_SHIFT ) )

#define SIGNAL_N2HET2_03_E2  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_03_SHIFT ) )
#define SIGNAL_N2HET2_03_D5  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_03_SHIFT ) )

#define SIGNAL_N2HET2_04_D13 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_04_SHIFT ) )
#define SIGNAL_N2HET2_04_H3  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_04_SHIFT ) )

#define SIGNAL_N2HET2_05_D12 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_05_SHIFT ) )
#define SIGNAL_N2HET2_05_D16 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_05_SHIFT ) )

#define SIGNAL_N2HET2_06_D11 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_06_SHIFT ) )
#define SIGNAL_N2HET2_06_M1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_06_SHIFT ) )

#define SIGNAL_N2HET2_07_N3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_07_SHIFT ) )
#define SIGNAL_N2HET2_07_N17 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_07_SHIFT ) )

#define SIGNAL_N2HET2_08_K16 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_08_SHIFT ) )
#define SIGNAL_N2HET2_08_V2  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_08_SHIFT ) )

#define SIGNAL_N2HET2_09_L16 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_09_SHIFT ) )
#define SIGNAL_N2HET2_09_K17 ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_09_SHIFT ) )

#define SIGNAL_N2HET2_10_M16 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_10_SHIFT ) )
#define SIGNAL_N2HET2_10_U1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_10_SHIFT ) )

#define SIGNAL_N2HET2_11_N16 ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_11_SHIFT ) )
#define SIGNAL_N2HET2_11_C4  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_11_SHIFT ) )

#define SIGNAL_N2HET2_12_D3  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_12_SHIFT ) )
#define SIGNAL_N2HET2_12_V6  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_12_SHIFT ) )

#define SIGNAL_N2HET2_13_D2  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_13_SHIFT ) )
#define SIGNAL_N2HET2_13_C5  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_13_SHIFT ) )

#define SIGNAL_N2HET2_14_D1  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_14_SHIFT ) )
#define SIGNAL_N2HET2_14_T1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_14_SHIFT ) )

#define SIGNAL_N2HET2_15_K4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_15_SHIFT ) )
#define SIGNAL_N2HET2_15_C6  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_15_SHIFT ) )

#define SIGNAL_N2HET2_16_L4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_16_SHIFT ) )
#define SIGNAL_N2HET2_16_V7  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_16_SHIFT ) )

#define SIGNAL_N2HET2_18_N4  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_18_SHIFT ) )
#define SIGNAL_N2HET2_18_E3  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_18_SHIFT ) )

#define SIGNAL_N2HET2_20_T5  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_20_SHIFT ) )
#define SIGNAL_N2HET2_20_N2  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_20_SHIFT ) )

#define SIGNAL_N2HET2_22_T7  ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_N2HET2_22_SHIFT ) )
#define SIGNAL_N2HET2_22_N1  ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_N2HET2_22_SHIFT ) )

#define SIGNAL_nTZ1_1_N19    ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_nTZ1_1_SHIFT ) )
#define SIGNAL_nTZ1_1_C3     ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_nTZ1_1_SHIFT ) )

#define SIGNAL_nTZ1_2_F1     ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_nTZ1_2_SHIFT ) )
#define SIGNAL_nTZ1_2_B2     ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_nTZ1_2_SHIFT ) )

#define SIGNAL_nTZ1_3_J3     ( ( uint32 ) ( ( uint32 ) 0x1U << SIGNAL_nTZ1_3_SHIFT ) )
#define SIGNAL_nTZ1_3_D19    ( ( uint32 ) ( ( uint32 ) 0x2U << SIGNAL_nTZ1_3_SHIFT ) )

/** @fn void muxInit(void)
 *   @brief Initializes the PINMUX Driver
 *
 *   This function initializes the PINMUX module and configures the selected
 *   pinmux settings as per the user selection in the GUI
 */
void muxInit( void );

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

#endif
