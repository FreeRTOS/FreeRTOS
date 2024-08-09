/** @file pinmux.c
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

/* Include Files */

#include "pinmux.h"

#define PINMUX_GIOB_DISABLE_HET2_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 179 ] = ( pinMuxReg->PINMUX[ 179 ]          \
                                   & PINMUX_GIOB_DISABLE_HET2_MASK ) \
                               | ( PINMUX_GIOB_DISABLE_HET2_##state ) )

#define PINMUX_GIOA_DISABLE_HET1_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 179 ] = ( pinMuxReg->PINMUX[ 179 ]          \
                                   & PINMUX_GIOB_DISABLE_HET2_MASK ) \
                               | ( PINMUX_GIOB_DISABLE_HET2_##state ) )

#define PINMUX_ETHERNET_SELECT( interface )                                          \
    ( pinMuxReg->PINMUX[ 160 ] = ( pinMuxReg->PINMUX[ 160 ] & PINMUX_ETHERNET_MASK ) \
                               | ( PINMUX_ETHERNET_##interface ) )

#define PINMUX_ETPWM1_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 167 ] = ( pinMuxReg->PINMUX[ 167 ] & PINMUX_ETPWM1_MASK ) \
                               | ( PINMUX_ETPWM1_##interface ) )

#define PINMUX_ETPWM2_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 167 ] = ( pinMuxReg->PINMUX[ 167 ] & PINMUX_ETPWM2_MASK ) \
                               | ( PINMUX_ETPWM2_##interface ) )

#define PINMUX_ETPWM3_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 167 ] = ( pinMuxReg->PINMUX[ 167 ] & PINMUX_ETPWM3_MASK ) \
                               | ( PINMUX_ETPWM3_##interface ) )

#define PINMUX_ETPWM4_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 167 ] = ( pinMuxReg->PINMUX[ 167 ] & PINMUX_ETPWM4_MASK ) \
                               | ( PINMUX_ETPWM4_##interface ) )

#define PINMUX_ETPWM5_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 168 ] = ( pinMuxReg->PINMUX[ 168 ] & PINMUX_ETPWM5_MASK ) \
                               | ( PINMUX_ETPWM5_##interface ) )

#define PINMUX_ETPWM6_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 168 ] = ( pinMuxReg->PINMUX[ 168 ] & PINMUX_ETPWM6_MASK ) \
                               | ( PINMUX_ETPWM6_##interface ) )

#define PINMUX_ETPWM7_EQEPERR_ENABLE( interface )                                  \
    ( pinMuxReg->PINMUX[ 168 ] = ( pinMuxReg->PINMUX[ 168 ] & PINMUX_ETPWM7_MASK ) \
                               | ( PINMUX_ETPWM7_##interface ) )

#define PINMUX_ETPWM_TZ1_ENABLE( interface )                                    \
    ( pinMuxReg->PINMUX[ 172 ] = ( pinMuxReg->PINMUX[ 172 ] & PINMUX_TZ1_MASK ) \
                               | ( PINMUX_TZ1_##interface ) )

#define PINMUX_ETPWM_TZ2_ENABLE( interface )                                    \
    ( pinMuxReg->PINMUX[ 172 ] = ( pinMuxReg->PINMUX[ 172 ] & PINMUX_TZ2_MASK ) \
                               | ( PINMUX_TZ2_##interface ) )

#define PINMUX_ETPWM_TZ3_ENABLE( interface )                                    \
    ( pinMuxReg->PINMUX[ 173 ] = ( pinMuxReg->PINMUX[ 173 ] & PINMUX_TZ3_MASK ) \
                               | ( PINMUX_TZ3_##interface ) )

#define PINMUX_ETPWM_EPWM1SYNCI_ENABLE( interface )                                    \
    ( pinMuxReg->PINMUX[ 173 ] = ( pinMuxReg->PINMUX[ 173 ] & PINMUX_EPWM1SYNCI_MASK ) \
                               | ( PINMUX_EPWM1SYNCI_##interface ) )

#define PINMUX_ETPWM_TIME_BASE_SYNC_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 165 ] = ( pinMuxReg->PINMUX[ 165 ]             \
                                   & PINMUX_ETPWM_TIME_BASE_SYNC_MASK ) \
                               | ( PINMUX_ETPWM_TIME_BASE_SYNC_##state ) )

#define PINMUX_ETPWM_SOC1A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 164 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC1A_MASK ) \
                               | ( PINMUX_ETPWM_SOC1A_##state ) )

#define PINMUX_ETPWM_SOC2A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 164 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC2A_MASK ) \
                               | ( PINMUX_ETPWM_SOC2A_##state ) )

#define PINMUX_ETPWM_SOC3A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 164 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC3A_MASK ) \
                               | ( PINMUX_ETPWM_SOC3A_##state ) )

#define PINMUX_ETPWM_SOC4A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 164 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC4A_MASK ) \
                               | ( PINMUX_ETPWM_SOC4A_##state ) )

#define PINMUX_ETPWM_SOC5A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 165 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC5A_MASK ) \
                               | ( PINMUX_ETPWM_SOC5A_##state ) )

#define PINMUX_ETPWM_SOC6A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 165 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC6A_MASK ) \
                               | ( PINMUX_ETPWM_SOC6A_##state ) )

#define PINMUX_ETPWM_SOC7A_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 165 ] = ( pinMuxReg->PINMUX[ 164 ] & PINMUX_ETPWM_SOC7A_MASK ) \
                               | ( PINMUX_ETPWM_SOC7A_##state ) )

#define PINMUX_GATE_EMIF_CLK_ENABLE( state )                                          \
    ( pinMuxReg->PINMUX[ 9 ] = ( pinMuxReg->PINMUX[ 9 ] & PINMUX_GATE_EMIF_CLK_MASK ) \
                             | ( PINMUX_GATE_EMIF_CLK_##state ) )

#define PINMUX_ALT_ADC_TRIGGER_SELECT( num )                       \
    ( pinMuxReg->PINMUX[ 161 ] = ( pinMuxReg->PINMUX[ 161 ]        \
                                   & PINMUX_ALT_ADC_TRIGGER_MASK ) \
                               | ( PINMUX_ALT_ADC_TRIGGER_##num ) )

#define PINMUX_EMIF_OUTPUT_ENABLE( state )                            \
    ( pinMuxReg->PINMUX[ 174 ] = ( pinMuxReg->PINMUX[ 174 ]           \
                                   & PINMUX_EMIF_OUTPUT_ENABLE_MASK ) \
                               | ( PINMUX_EMIF_OUTPUT_ENABLE_##state ) )

#define PINMUX_EQEP1A_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 170 ] = ( pinMuxReg->PINMUX[ 170 ]      \
                                   & PINMUX_EQEP1A_FILTER_MASK ) \
                               | ( PINMUX_EQEP1A_FILTER_##state ) )

#define PINMUX_EQEP1B_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 170 ] = ( pinMuxReg->PINMUX[ 170 ]      \
                                   & PINMUX_EQEP1B_FILTER_MASK ) \
                               | ( PINMUX_EQEP1B_FILTER_##state ) )

#define PINMUX_EQEP1I_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 171 ] = ( pinMuxReg->PINMUX[ 171 ]      \
                                   & PINMUX_EQEP1I_FILTER_MASK ) \
                               | ( PINMUX_EQEP1I_FILTER_##state ) )

#define PINMUX_EQEP1S_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 171 ] = ( pinMuxReg->PINMUX[ 171 ]      \
                                   & PINMUX_EQEP1S_FILTER_MASK ) \
                               | ( PINMUX_EQEP1S_FILTER_##state ) )

#define PINMUX_EQEP2A_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 171 ] = ( pinMuxReg->PINMUX[ 171 ]      \
                                   & PINMUX_EQEP2A_FILTER_MASK ) \
                               | ( PINMUX_EQEP2A_FILTER_##state ) )

#define PINMUX_EQEP2B_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 171 ] = ( pinMuxReg->PINMUX[ 171 ]      \
                                   & PINMUX_EQEP2B_FILTER_MASK ) \
                               | ( PINMUX_EQEP2B_FILTER_##state ) )

#define PINMUX_EQEP2I_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 172 ] = ( pinMuxReg->PINMUX[ 172 ]      \
                                   & PINMUX_EQEP2I_FILTER_MASK ) \
                               | ( PINMUX_EQEP2I_FILTER_##state ) )

#define PINMUX_EQEP2S_FILTER_ENABLE( state )                     \
    ( pinMuxReg->PINMUX[ 172 ] = ( pinMuxReg->PINMUX[ 172 ]      \
                                   & PINMUX_EQEP2S_FILTER_MASK ) \
                               | ( PINMUX_EQEP2S_FILTER_##state ) )

#define PINMUX_ECAP1_FILTER_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 169 ] = ( pinMuxReg->PINMUX[ 169 ] & PINMUX_ECAP1_FILTER_MASK ) \
                               | ( PINMUX_ECAP1_FILTER_##state ) )

#define PINMUX_ECAP2_FILTER_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 169 ] = ( pinMuxReg->PINMUX[ 169 ] & PINMUX_ECAP2_FILTER_MASK ) \
                               | ( PINMUX_ECAP2_FILTER_##state ) )

#define PINMUX_ECAP3_FILTER_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 169 ] = ( pinMuxReg->PINMUX[ 169 ] & PINMUX_ECAP3_FILTER_MASK ) \
                               | ( PINMUX_ECAP3_FILTER_##state ) )

#define PINMUX_ECAP4_FILTER_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 169 ] = ( pinMuxReg->PINMUX[ 169 ] & PINMUX_ECAP4_FILTER_MASK ) \
                               | ( PINMUX_ECAP4_FILTER_##state ) )

#define PINMUX_ECAP5_FILTER_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 170 ] = ( pinMuxReg->PINMUX[ 170 ] & PINMUX_ECAP5_FILTER_MASK ) \
                               | ( PINMUX_ECAP5_FILTER_##state ) )

#define PINMUX_ECAP6_FILTER_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 170 ] = ( pinMuxReg->PINMUX[ 170 ] & PINMUX_ECAP6_FILTER_MASK ) \
                               | ( PINMUX_ECAP6_FILTER_##state ) )

#define PINMUX_GIOA0_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 175 ] = ( pinMuxReg->PINMUX[ 175 ] & PINMUX_GIOA0_DMA_MASK ) \
                               | ( PINMUX_GIOA0_DMA_##state ) )

#define PINMUX_GIOA1_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 175 ] = ( pinMuxReg->PINMUX[ 175 ] & PINMUX_GIOA1_DMA_MASK ) \
                               | ( PINMUX_GIOA1_DMA_##state ) )

#define PINMUX_GIOA2_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 175 ] = ( pinMuxReg->PINMUX[ 175 ] & PINMUX_GIOA2_DMA_MASK ) \
                               | ( PINMUX_GIOA2_DMA_##state ) )

#define PINMUX_GIOA3_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 175 ] = ( pinMuxReg->PINMUX[ 175 ] & PINMUX_GIOA3_DMA_MASK ) \
                               | ( PINMUX_GIOA3_DMA_##state ) )

#define PINMUX_GIOA4_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 176 ] = ( pinMuxReg->PINMUX[ 176 ] & PINMUX_GIOA4_DMA_MASK ) \
                               | ( PINMUX_GIOA4_DMA_##state ) )

#define PINMUX_GIOA5_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 176 ] = ( pinMuxReg->PINMUX[ 176 ] & PINMUX_GIOA5_DMA_MASK ) \
                               | ( PINMUX_GIOA5_DMA_##state ) )

#define PINMUX_GIOA6_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 176 ] = ( pinMuxReg->PINMUX[ 176 ] & PINMUX_GIOA6_DMA_MASK ) \
                               | ( PINMUX_GIOA6_DMA_##state ) )

#define PINMUX_GIOA7_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 176 ] = ( pinMuxReg->PINMUX[ 176 ] & PINMUX_GIOA7_DMA_MASK ) \
                               | ( PINMUX_GIOA7_DMA_##state ) )

#define PINMUX_GIOB0_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 177 ] = ( pinMuxReg->PINMUX[ 177 ] & PINMUX_GIOB0_DMA_MASK ) \
                               | ( PINMUX_GIOB0_DMA_##state ) )

#define PINMUX_GIOB1_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 177 ] = ( pinMuxReg->PINMUX[ 177 ] & PINMUX_GIOB1_DMA_MASK ) \
                               | ( PINMUX_GIOB1_DMA_##state ) )

#define PINMUX_GIOB2_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 177 ] = ( pinMuxReg->PINMUX[ 177 ] & PINMUX_GIOB2_DMA_MASK ) \
                               | ( PINMUX_GIOB2_DMA_##state ) )

#define PINMUX_GIOB3_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 177 ] = ( pinMuxReg->PINMUX[ 177 ] & PINMUX_GIOB3_DMA_MASK ) \
                               | ( PINMUX_GIOB3_DMA_##state ) )

#define PINMUX_GIOB4_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 178 ] = ( pinMuxReg->PINMUX[ 178 ] & PINMUX_GIOB4_DMA_MASK ) \
                               | ( PINMUX_GIOB4_DMA_##state ) )

#define PINMUX_GIOB5_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 178 ] = ( pinMuxReg->PINMUX[ 178 ] & PINMUX_GIOB5_DMA_MASK ) \
                               | ( PINMUX_GIOB5_DMA_##state ) )

#define PINMUX_GIOB6_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 178 ] = ( pinMuxReg->PINMUX[ 178 ] & PINMUX_GIOB6_DMA_MASK ) \
                               | ( PINMUX_GIOB6_DMA_##state ) )

#define PINMUX_GIOB7_DMA_ENABLE( state )                                              \
    ( pinMuxReg->PINMUX[ 178 ] = ( pinMuxReg->PINMUX[ 178 ] & PINMUX_GIOB7_DMA_MASK ) \
                               | ( PINMUX_GIOB7_DMA_##state ) )

#define PINMUX_TEMP1_ENABLE( state )                                                     \
    ( pinMuxReg->PINMUX[ 173 ] = ( pinMuxReg->PINMUX[ 173 ] & PINMUX_TEMP1_ENABLE_MASK ) \
                               | ( PINMUX_TEMP1_ENABLE_##state ) )

#define PINMUX_TEMP2_ENABLE( state )                                                     \
    ( pinMuxReg->PINMUX[ 173 ] = ( pinMuxReg->PINMUX[ 173 ] & PINMUX_TEMP2_ENABLE_MASK ) \
                               | ( PINMUX_TEMP2_ENABLE_##state ) )

#define PINMUX_TEMP3_ENABLE( state )                                                     \
    ( pinMuxReg->PINMUX[ 174 ] = ( pinMuxReg->PINMUX[ 174 ] & PINMUX_TEMP3_ENABLE_MASK ) \
                               | ( PINMUX_TEMP3_ENABLE_##state ) )

/* USER CODE BEGIN (0) */
/* USER CODE END */

void muxInit( void )
{
    /* USER CODE BEGIN (1) */
    /* USER CODE END */

    /* Enable Pin Muxing */
    pinMuxReg->KICKER0 = 0x83E70B13U;
    pinMuxReg->KICKER1 = 0x95A4F1E0U;

    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    pinMuxReg->PINMUX[ 0 ] = PINMUX_BALL_N19_AD1EVT | PINMUX_BALL_D4_EMIF_ADDR_00
                           | PINMUX_BALL_D5_EMIF_ADDR_01 | PINMUX_BALL_C4_EMIF_ADDR_06;

    pinMuxReg->PINMUX[ 1 ] = PINMUX_BALL_C5_EMIF_ADDR_07 | PINMUX_BALL_C6_EMIF_ADDR_08
                           | PINMUX_BALL_C7_EMIF_ADDR_09 | PINMUX_BALL_C8_EMIF_ADDR_10;

    pinMuxReg->PINMUX[ 2 ] = PINMUX_BALL_C9_EMIF_ADDR_11 | PINMUX_BALL_C10_EMIF_ADDR_12
                           | PINMUX_BALL_C11_EMIF_ADDR_13 | PINMUX_BALL_C12_EMIF_ADDR_14;

    pinMuxReg->PINMUX[ 3 ] = PINMUX_BALL_C13_EMIF_ADDR_15 | PINMUX_BALL_D14_EMIF_ADDR_16
                           | PINMUX_BALL_C14_EMIF_ADDR_17 | PINMUX_BALL_D15_EMIF_ADDR_18;

    pinMuxReg->PINMUX[ 4 ] = PINMUX_BALL_C15_EMIF_ADDR_19 | PINMUX_BALL_C16_EMIF_ADDR_20
                           | PINMUX_BALL_C17_EMIF_ADDR_21;

    pinMuxReg->PINMUX[ 5 ] = 0U;

    pinMuxReg->PINMUX[ 6 ] = 0U;

    pinMuxReg->PINMUX[ 7 ] = 0U;

    pinMuxReg->PINMUX[ 8 ] = PINMUX_BALL_D16_EMIF_BA_1;

    pinMuxReg->PINMUX[ 9 ] = PINMUX_BALL_R4_EMIF_nCAS | PINMUX_BALL_N17_EMIF_nCS_0
                           | PINMUX_BALL_L17_EMIF_nCS_2;

    pinMuxReg->PINMUX[ 10 ] = PINMUX_BALL_K17_EMIF_nCS_3 | PINMUX_BALL_M17_EMIF_nCS_4
                            | PINMUX_BALL_R3_EMIF_nRAS | PINMUX_BALL_P3_EMIF_nWAIT;

    pinMuxReg->PINMUX[ 11 ] = PINMUX_BALL_D17_EMIF_nWE | PINMUX_BALL_E9_ETMDATA_08
                            | PINMUX_BALL_E8_ETMDATA_09 | PINMUX_BALL_E7_ETMDATA_10;

    pinMuxReg->PINMUX[ 12 ] = PINMUX_BALL_E6_ETMDATA_11 | PINMUX_BALL_E13_ETMDATA_12
                            | PINMUX_BALL_E12_ETMDATA_13 | PINMUX_BALL_E11_ETMDATA_14;

    pinMuxReg->PINMUX[ 13 ] = PINMUX_BALL_E10_ETMDATA_15 | PINMUX_BALL_K15_ETMDATA_16
                            | PINMUX_BALL_L15_ETMDATA_17 | PINMUX_BALL_M15_ETMDATA_18;

    pinMuxReg->PINMUX[ 14 ] = PINMUX_BALL_N15_ETMDATA_19 | PINMUX_BALL_E5_ETMDATA_20
                            | PINMUX_BALL_F5_ETMDATA_21 | PINMUX_BALL_G5_ETMDATA_22;

    pinMuxReg->PINMUX[ 15 ] = PINMUX_BALL_K5_ETMDATA_23 | PINMUX_BALL_L5_ETMDATA_24
                            | PINMUX_BALL_M5_ETMDATA_25 | PINMUX_BALL_N5_ETMDATA_26;

    pinMuxReg->PINMUX[ 16 ] = PINMUX_BALL_P5_ETMDATA_27 | PINMUX_BALL_R5_ETMDATA_28
                            | PINMUX_BALL_R6_ETMDATA_29 | PINMUX_BALL_R7_ETMDATA_30;

    pinMuxReg->PINMUX[ 17 ] = PINMUX_BALL_R8_ETMDATA_31 | PINMUX_BALL_R9_ETMTRACECLKIN
                            | PINMUX_BALL_R10_ETMTRACECLKOUT
                            | PINMUX_BALL_R11_ETMTRACECTL;

    pinMuxReg->PINMUX[ 18 ] = PINMUX_BALL_B15_FRAYTX1 | PINMUX_BALL_B8_FRAYTX2
                            | PINMUX_BALL_B16_FRAYTXEN1 | PINMUX_BALL_B9_FRAYTXEN2;

    pinMuxReg->PINMUX[ 19 ] = PINMUX_BALL_C1_GIOA_2 | PINMUX_BALL_E1_GIOA_3
                            | PINMUX_BALL_B5_GIOA_5 | PINMUX_BALL_H3_GIOA_6;

    pinMuxReg->PINMUX[ 20 ] = PINMUX_BALL_M1_GIOA_7 | PINMUX_BALL_F2_GIOB_2
                            | PINMUX_BALL_W10_GIOB_3 | PINMUX_BALL_J2_GIOB_6;

    pinMuxReg->PINMUX[ 21 ] = PINMUX_BALL_F1_GIOB_7 | PINMUX_BALL_R2_MIBSPI1NCS_0
                            | PINMUX_BALL_F3_MIBSPI1NCS_1 | PINMUX_BALL_G3_MIBSPI1NCS_2;

    pinMuxReg->PINMUX[ 22 ] = PINMUX_BALL_J3_MIBSPI1NCS_3 | PINMUX_BALL_G19_MIBSPI1NENA
                            | PINMUX_BALL_V9_MIBSPI3CLK | PINMUX_BALL_V10_MIBSPI3NCS_0;

    pinMuxReg->PINMUX[ 23 ] = PINMUX_BALL_V5_MIBSPI3NCS_1 | PINMUX_BALL_B2_MIBSPI3NCS_2
                            | PINMUX_BALL_C3_MIBSPI3NCS_3 | PINMUX_BALL_W9_MIBSPI3NENA;

    pinMuxReg->PINMUX[ 24 ] = PINMUX_BALL_W8_MIBSPI3SIMO | PINMUX_BALL_V8_MIBSPI3SOMI
                            | PINMUX_BALL_H19_MIBSPI5CLK | PINMUX_BALL_E19_MIBSPI5NCS_0;

    pinMuxReg->PINMUX[ 25 ] = PINMUX_BALL_B6_MIBSPI5NCS_1 | PINMUX_BALL_W6_MIBSPI5NCS_2
                            | PINMUX_BALL_T12_MIBSPI5NCS_3 | PINMUX_BALL_H18_MIBSPI5NENA;

    pinMuxReg->PINMUX[ 26 ] = PINMUX_BALL_J19_MIBSPI5SIMO_0
                            | PINMUX_BALL_E16_MIBSPI5SIMO_1
                            | PINMUX_BALL_H17_MIBSPI5SIMO_2
                            | PINMUX_BALL_G17_MIBSPI5SIMO_3;

    pinMuxReg->PINMUX[ 27 ] = PINMUX_BALL_J18_MIBSPI5SOMI_0
                            | PINMUX_BALL_E17_MIBSPI5SOMI_1
                            | PINMUX_BALL_H16_MIBSPI5SOMI_2
                            | PINMUX_BALL_G16_MIBSPI5SOMI_3;

    pinMuxReg->PINMUX[ 28 ] = PINMUX_BALL_K18_N2HET1_00 | PINMUX_BALL_V2_N2HET1_01
                            | PINMUX_BALL_W5_N2HET1_02 | PINMUX_BALL_U1_N2HET1_03;

    pinMuxReg->PINMUX[ 29 ] = PINMUX_BALL_B12_N2HET1_04 | PINMUX_BALL_V6_N2HET1_05
                            | PINMUX_BALL_W3_N2HET1_06 | PINMUX_BALL_T1_N2HET1_07;

    pinMuxReg->PINMUX[ 30 ] = PINMUX_BALL_E18_N2HET1_08 | PINMUX_BALL_V7_N2HET1_09
                            | PINMUX_BALL_D19_N2HET1_10 | PINMUX_BALL_E3_N2HET1_11;

    pinMuxReg->PINMUX[ 31 ] = PINMUX_BALL_B4_N2HET1_12 | PINMUX_BALL_N2_N2HET1_13
                            | PINMUX_BALL_N1_N2HET1_15 | PINMUX_BALL_A4_N2HET1_16;

    pinMuxReg->PINMUX[ 32 ] = PINMUX_BALL_A13_N2HET1_17 | PINMUX_BALL_J1_N2HET1_18
                            | PINMUX_BALL_B13_N2HET1_19 | PINMUX_BALL_P2_N2HET1_20;

    pinMuxReg->PINMUX[ 33 ] = PINMUX_BALL_H4_N2HET1_21 | PINMUX_BALL_B3_N2HET1_22
                            | PINMUX_BALL_J4_N2HET1_23 | PINMUX_BALL_P1_N2HET1_24;

    pinMuxReg->PINMUX[ 34 ] = PINMUX_BALL_A14_N2HET1_26 | PINMUX_BALL_K19_N2HET1_28
                            | PINMUX_BALL_B11_N2HET1_30 | PINMUX_BALL_D8_N2HET2_01;

    pinMuxReg->PINMUX[ 35 ] = PINMUX_BALL_D7_N2HET2_02 | PINMUX_BALL_D3_N2HET2_12
                            | PINMUX_BALL_D2_N2HET2_13 | PINMUX_BALL_D1_N2HET2_14;

    pinMuxReg->PINMUX[ 36 ] = PINMUX_BALL_P4_N2HET2_19 | PINMUX_BALL_T5_N2HET2_20
                            | PINMUX_BALL_T4_MII_RXCLK | PINMUX_BALL_U7_MII_TX_CLK;

    pinMuxReg->PINMUX[ 37 ] = PINMUX_BALL_E2_N2HET2_03 | PINMUX_BALL_N3_N2HET2_07;

    pinMuxReg->PINMUX[ 80 ] = ( SIGNAL_AD2EVT_T10 | 0x02020200U );

    pinMuxReg->PINMUX[ 81 ] = 0x02020202U;

    pinMuxReg->PINMUX[ 82 ] = 0x02020202U;

    pinMuxReg->PINMUX[ 83 ] = ( SIGNAL_GIOA_0_A5 | 0x00020202U );

    pinMuxReg->PINMUX[ 84 ] = SIGNAL_GIOA_1_C2 | SIGNAL_GIOA_2_C1 | SIGNAL_GIOA_3_E1
                            | SIGNAL_GIOA_4_A6;

    pinMuxReg->PINMUX[ 85 ] = SIGNAL_GIOA_5_B5 | SIGNAL_GIOA_6_H3 | SIGNAL_GIOA_7_M1
                            | SIGNAL_GIOB_0_M2;

    pinMuxReg->PINMUX[ 86 ] = SIGNAL_GIOB_1_K2 | SIGNAL_GIOB_2_F2 | SIGNAL_GIOB_3_W10
                            | SIGNAL_GIOB_4_G1;

    pinMuxReg->PINMUX[ 87 ] = SIGNAL_GIOB_5_G2 | SIGNAL_GIOB_6_J2 | SIGNAL_GIOB_7_F1
                            | SIGNAL_MDIO_F4;

    pinMuxReg->PINMUX[ 88 ] = ( SIGNAL_MIBSPI1NCS_4_U10 | SIGNAL_MIBSPI1NCS_5_U9
                                | 0x00020000U );

    pinMuxReg->PINMUX[ 89 ] = SIGNAL_MII_COL_W4 | SIGNAL_MII_CRS_V4;

    pinMuxReg->PINMUX[ 90 ] = SIGNAL_MII_RX_DV_U6 | SIGNAL_MII_RX_ER_U5
                            | SIGNAL_MII_RXCLK_T4 | SIGNAL_MII_RXD_0_U4;

    pinMuxReg->PINMUX[ 91 ] = SIGNAL_MII_RXD_1_T3 | SIGNAL_MII_RXD_2_U3
                            | SIGNAL_MII_RXD_3_V3 | SIGNAL_MII_TX_CLK_U7;

    pinMuxReg->PINMUX[ 92 ] = SIGNAL_N2HET1_17_A13 | SIGNAL_N2HET1_19_B13
                            | SIGNAL_N2HET1_21_H4 | SIGNAL_N2HET1_23_J4;

    pinMuxReg->PINMUX[ 93 ] = SIGNAL_N2HET1_25_M3 | SIGNAL_N2HET1_27_A9
                            | SIGNAL_N2HET1_29_A3 | SIGNAL_N2HET1_31_J17;

    pinMuxReg->PINMUX[ 94 ] = SIGNAL_N2HET2_00_D6 | SIGNAL_N2HET2_01_D8
                            | SIGNAL_N2HET2_02_D7 | SIGNAL_N2HET2_03_E2;

    pinMuxReg->PINMUX[ 95 ] = SIGNAL_N2HET2_04_D13 | SIGNAL_N2HET2_05_D12
                            | SIGNAL_N2HET2_06_D11 | SIGNAL_N2HET2_07_N3;

    pinMuxReg->PINMUX[ 96 ] = SIGNAL_N2HET2_08_K16 | SIGNAL_N2HET2_09_L16
                            | SIGNAL_N2HET2_10_M16 | SIGNAL_N2HET2_11_N16;

    pinMuxReg->PINMUX[ 97 ] = SIGNAL_N2HET2_12_D3 | SIGNAL_N2HET2_13_D2
                            | SIGNAL_N2HET2_14_D1 | SIGNAL_N2HET2_15_K4;

    pinMuxReg->PINMUX[ 98 ] = SIGNAL_N2HET2_16_L4 | SIGNAL_N2HET2_18_N4
                            | SIGNAL_N2HET2_20_T5 | SIGNAL_N2HET2_22_T7;

    pinMuxReg->PINMUX[ 99 ] = SIGNAL_nTZ1_1_N19 | SIGNAL_nTZ1_2_F1 | SIGNAL_nTZ1_3_J3;

    pinMuxReg->PINMUX[ 161 ] = 0x02020200U;

    pinMuxReg->PINMUX[ 162 ] = 0x02020202U;

    pinMuxReg->PINMUX[ 163 ] = 0x00020202U;

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    PINMUX_GATE_EMIF_CLK_ENABLE( OFF );
    PINMUX_EMIF_OUTPUT_ENABLE( OFF );
    PINMUX_GIOA_DISABLE_HET1_ENABLE( OFF );
    PINMUX_GIOB_DISABLE_HET2_ENABLE( OFF );
    PINMUX_ETHERNET_SELECT( MII );
    PINMUX_ALT_ADC_TRIGGER_SELECT( 1 );

    PINMUX_ETPWM1_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM2_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM3_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM4_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM5_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM6_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM7_EQEPERR_ENABLE( EQEPERR12 );
    PINMUX_ETPWM_TIME_BASE_SYNC_ENABLE( OFF );
    PINMUX_ETPWM_TZ1_ENABLE( ASYNC );
    PINMUX_ETPWM_TZ2_ENABLE( ASYNC );
    PINMUX_ETPWM_TZ3_ENABLE( ASYNC );
    PINMUX_ETPWM_EPWM1SYNCI_ENABLE( ASYNC );

    PINMUX_ETPWM_SOC1A_ENABLE( ON );
    PINMUX_ETPWM_SOC2A_ENABLE( ON );
    PINMUX_ETPWM_SOC3A_ENABLE( ON );
    PINMUX_ETPWM_SOC4A_ENABLE( ON );
    PINMUX_ETPWM_SOC5A_ENABLE( ON );
    PINMUX_ETPWM_SOC6A_ENABLE( ON );
    PINMUX_ETPWM_SOC7A_ENABLE( ON );

    PINMUX_EQEP1A_FILTER_ENABLE( OFF );
    PINMUX_EQEP1B_FILTER_ENABLE( OFF );
    PINMUX_EQEP1I_FILTER_ENABLE( OFF );
    PINMUX_EQEP1S_FILTER_ENABLE( OFF );
    PINMUX_EQEP2A_FILTER_ENABLE( OFF );
    PINMUX_EQEP2B_FILTER_ENABLE( OFF );
    PINMUX_EQEP2I_FILTER_ENABLE( OFF );
    PINMUX_EQEP2S_FILTER_ENABLE( OFF );

    PINMUX_ECAP1_FILTER_ENABLE( OFF );
    PINMUX_ECAP2_FILTER_ENABLE( OFF );
    PINMUX_ECAP3_FILTER_ENABLE( OFF );
    PINMUX_ECAP4_FILTER_ENABLE( OFF );
    PINMUX_ECAP5_FILTER_ENABLE( OFF );
    PINMUX_ECAP6_FILTER_ENABLE( OFF );

    PINMUX_GIOA0_DMA_ENABLE( OFF );
    PINMUX_GIOA1_DMA_ENABLE( OFF );
    PINMUX_GIOA2_DMA_ENABLE( OFF );
    PINMUX_GIOA3_DMA_ENABLE( OFF );
    PINMUX_GIOA4_DMA_ENABLE( OFF );
    PINMUX_GIOA5_DMA_ENABLE( OFF );
    PINMUX_GIOA6_DMA_ENABLE( OFF );
    PINMUX_GIOA7_DMA_ENABLE( OFF );
    PINMUX_GIOB0_DMA_ENABLE( OFF );
    PINMUX_GIOB1_DMA_ENABLE( OFF );
    PINMUX_GIOB2_DMA_ENABLE( OFF );
    PINMUX_GIOB3_DMA_ENABLE( OFF );
    PINMUX_GIOB4_DMA_ENABLE( OFF );
    PINMUX_GIOB5_DMA_ENABLE( OFF );
    PINMUX_GIOB6_DMA_ENABLE( OFF );
    PINMUX_GIOB7_DMA_ENABLE( OFF );

    pinMuxReg->PINMUX[ 174 ] |= ( uint32 ) ( ~( 0XFEFFFFFFU ) );

    PINMUX_TEMP1_ENABLE( OFF );
    PINMUX_TEMP2_ENABLE( OFF );
    PINMUX_TEMP3_ENABLE( OFF );

    /* Disable Pin Muxing */
    pinMuxReg->KICKER0 = 0x00000000U;
    pinMuxReg->KICKER1 = 0x00000000U;

    /* USER CODE BEGIN (4) */
    /* USER CODE END */
}

/* USER CODE BEGIN (5) */
/* USER CODE END */
