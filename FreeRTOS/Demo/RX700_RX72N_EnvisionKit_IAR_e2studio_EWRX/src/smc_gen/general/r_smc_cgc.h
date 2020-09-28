/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_smc_cgc.h
* Version      : 1.6.101
* Device(s)    : R5F572NNHxFB
* Description  : CGC setting header file.
***********************************************************************************************************************/

#ifndef SMC_CGC_H
#define SMC_CGC_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    PLL Control Register (PLLCR)
*/
/* PLL Input Frequency Division Ratio Select (PLIDIV[1:0]) */
#define _0000_CGC_PLL_FREQ_DIV_1            (0x0000U) /* x1 */
#define _0001_CGC_PLL_FREQ_DIV_2            (0x0001U) /* x1/2 */
#define _0002_CGC_PLL_FREQ_DIV_3            (0x0002U) /* x1/3 */
/* PLL Clock Source Select (PLLSRCSEL) */
#define _0000_CGC_PLL_SOURCE_MAIN           (0x0000U) /* Main clock oscillator */
#define _0010_CGC_PLL_SOURCE_HOCO           (0x0010U) /* HOCO */
/* Frequency Multiplication Factor Select (STC[5:0]) */
#define _1300_CGC_PLL_FREQ_MUL_10_0         (0x1300U) /* x10.0 */
#define _1400_CGC_PLL_FREQ_MUL_10_5         (0x1400U) /* x10.5 */
#define _1500_CGC_PLL_FREQ_MUL_11_0         (0x1500U) /* x11.0 */
#define _1600_CGC_PLL_FREQ_MUL_11_5         (0x1600U) /* x11.5 */
#define _1700_CGC_PLL_FREQ_MUL_12_0         (0x1700U) /* x12.0 */
#define _1800_CGC_PLL_FREQ_MUL_12_5         (0x1800U) /* x12.5 */
#define _1900_CGC_PLL_FREQ_MUL_13_0         (0x1900U) /* x13.0 */
#define _1A00_CGC_PLL_FREQ_MUL_13_5         (0x1A00U) /* x13.5 */
#define _1B00_CGC_PLL_FREQ_MUL_14_0         (0x1B00U) /* x14.0 */
#define _1C00_CGC_PLL_FREQ_MUL_14_5         (0x1C00U) /* x14.5 */
#define _1D00_CGC_PLL_FREQ_MUL_15_0         (0x1D00U) /* x15.0 */
#define _1E00_CGC_PLL_FREQ_MUL_15_5         (0x1E00U) /* x15.5 */
#define _1F00_CGC_PLL_FREQ_MUL_16_0         (0x1F00U) /* x16.0 */
#define _2000_CGC_PLL_FREQ_MUL_16_5         (0x2000U) /* x16.5 */
#define _2100_CGC_PLL_FREQ_MUL_17_0         (0x2100U) /* x17.0 */
#define _2200_CGC_PLL_FREQ_MUL_17_5         (0x2200U) /* x17.5 */
#define _2300_CGC_PLL_FREQ_MUL_18_0         (0x2300U) /* x18.0 */
#define _2400_CGC_PLL_FREQ_MUL_18_5         (0x2400U) /* x18.5 */
#define _2500_CGC_PLL_FREQ_MUL_19_0         (0x2500U) /* x19.0 */
#define _2600_CGC_PLL_FREQ_MUL_19_5         (0x2600U) /* x19.5 */
#define _2700_CGC_PLL_FREQ_MUL_20_0         (0x2700U) /* x20.0 */
#define _2800_CGC_PLL_FREQ_MUL_20_5         (0x2800U) /* x20.5 */
#define _2900_CGC_PLL_FREQ_MUL_21_0         (0x2900U) /* x21.0 */
#define _2A00_CGC_PLL_FREQ_MUL_21_5         (0x2A00U) /* x21.5 */
#define _2B00_CGC_PLL_FREQ_MUL_22_0         (0x2B00U) /* x22.0 */
#define _2C00_CGC_PLL_FREQ_MUL_22_5         (0x2C00U) /* x22.5 */
#define _2D00_CGC_PLL_FREQ_MUL_23_0         (0x2D00U) /* x23.0 */
#define _2E00_CGC_PLL_FREQ_MUL_23_5         (0x2E00U) /* x23.5 */
#define _2F00_CGC_PLL_FREQ_MUL_24_0         (0x2F00U) /* x24.0 */
#define _3000_CGC_PLL_FREQ_MUL_24_5         (0x3000U) /* x24.5 */
#define _3100_CGC_PLL_FREQ_MUL_25_0         (0x3100U) /* x25.0 */
#define _3200_CGC_PLL_FREQ_MUL_25_5         (0x3200U) /* x25.5 */
#define _3300_CGC_PLL_FREQ_MUL_26_0         (0x3300U) /* x26.0 */
#define _3400_CGC_PLL_FREQ_MUL_26_5         (0x3400U) /* x26.5 */
#define _3500_CGC_PLL_FREQ_MUL_27_0         (0x3500U) /* x27.0 */
#define _3600_CGC_PLL_FREQ_MUL_27_5         (0x3600U) /* x27.5 */
#define _3700_CGC_PLL_FREQ_MUL_28_0         (0x3700U) /* x28.0 */
#define _3800_CGC_PLL_FREQ_MUL_28_5         (0x3800U) /* x28.5 */
#define _3900_CGC_PLL_FREQ_MUL_29_0         (0x3900U) /* x29.0 */
#define _3A00_CGC_PLL_FREQ_MUL_29_5         (0x3A00U) /* x29.5 */
#define _3B00_CGC_PLL_FREQ_MUL_30_0         (0x3B00U) /* x30.0 */

/*
    High-Speed On-Chip Oscillator Control Register 2 (HOCOCR2)
*/
/* HOCO Frequency Setting (HCFRQ[1:0]) */
#define _00_CGC_HOCO_CLK_16                 (0x00U) /* 16 MHz */
#define _01_CGC_HOCO_CLK_18                 (0x01U) /* 18 MHz */
#define _02_CGC_HOCO_CLK_20                 (0x02U) /* 20 MHz */

/*
    Main Clock Oscillator Forced Oscillation Control Register (MOFCR)
*/
/* Main Clock Oscillator Forced Oscillation (MOFXIN) */
#define _00_CGC_MAINOSC_NOT_CONTROLLED      (0x00U) /* Oscillator is not controlled by this bit */
#define _01_CGC_MAINOSC_FORCE_OSCILLATED    (0x01U) /* The main clock oscillator is forcedly oscillated */
/* Main Oscillator Drive Capability 2 Switching (MODRV2[1:0]) */
#define _00_CGC_MAINOSC_UNDER24M            (0x00U) /* 20.1 to 24 MHz */
#define _10_CGC_MAINOSC_UNDER20M            (0x10U) /* 16.1 to 20 MHz */
#define _20_CGC_MAINOSC_UNDER16M            (0x20U) /* 8.1 to 16 MHz */
#define _30_CGC_MAINOSC_EQUATE8M            (0x30U) /* 8 MHz */
/* Main Clock Oscillator Switch (MOSEL) */
#define _00_CGC_MAINOSC_RESONATOR           (0x00U) /* Resonator */
#define _40_CGC_MAINOSC_EXTERNAL            (0x40U) /* External oscillator input */

/*
    PPLL Control Register (PPLLCR)
*/
/* PPLL Input Pulse Frequency Division Ratio Select (PPLIDIV[1:0]) */
#define _0000_CGC_PPLL_FREQ_DIV_1           (0x0000U) /* x1 */
#define _0001_CGC_PPLL_FREQ_DIV_2           (0x0001U) /* x1/2 */
#define _0002_CGC_PPLL_FREQ_DIV_3           (0x0002U) /* x1/3 */
/* PPLL Frequency Multiplier Setting (PPLSTC[5:0]) */
#define _1300_CGC_PPLL_FREQ_MUL_10_0        (0x1300U) /* x10.0 */
#define _1400_CGC_PPLL_FREQ_MUL_10_5        (0x1400U) /* x10.5 */
#define _1500_CGC_PPLL_FREQ_MUL_11_0        (0x1500U) /* x11.0 */
#define _1600_CGC_PPLL_FREQ_MUL_11_5        (0x1600U) /* x11.5 */
#define _1700_CGC_PPLL_FREQ_MUL_12_0        (0x1700U) /* x12.0 */
#define _1800_CGC_PPLL_FREQ_MUL_12_5        (0x1800U) /* x12.5 */
#define _1900_CGC_PPLL_FREQ_MUL_13_0        (0x1900U) /* x13.0 */
#define _1A00_CGC_PPLL_FREQ_MUL_13_5        (0x1A00U) /* x13.5 */
#define _1B00_CGC_PPLL_FREQ_MUL_14_0        (0x1B00U) /* x14.0 */
#define _1C00_CGC_PPLL_FREQ_MUL_14_5        (0x1C00U) /* x14.5 */
#define _1D00_CGC_PPLL_FREQ_MUL_15_0        (0x1D00U) /* x15.0 */
#define _1E00_CGC_PPLL_FREQ_MUL_15_5        (0x1E00U) /* x15.5 */
#define _1F00_CGC_PPLL_FREQ_MUL_16_0        (0x1F00U) /* x16.0 */
#define _2000_CGC_PPLL_FREQ_MUL_16_5        (0x2000U) /* x16.5 */
#define _2100_CGC_PPLL_FREQ_MUL_17_0        (0x2100U) /* x17.0 */
#define _2200_CGC_PPLL_FREQ_MUL_17_5        (0x2200U) /* x17.5 */
#define _2300_CGC_PPLL_FREQ_MUL_18_0        (0x2300U) /* x18.0 */
#define _2400_CGC_PPLL_FREQ_MUL_18_5        (0x2400U) /* x18.5 */
#define _2500_CGC_PPLL_FREQ_MUL_19_0        (0x2500U) /* x19.0 */
#define _2600_CGC_PPLL_FREQ_MUL_19_5        (0x2600U) /* x19.5 */
#define _2700_CGC_PPLL_FREQ_MUL_20_0        (0x2700U) /* x20.0 */
#define _2800_CGC_PPLL_FREQ_MUL_20_5        (0x2800U) /* x20.5 */
#define _2900_CGC_PPLL_FREQ_MUL_21_0        (0x2900U) /* x21.0 */
#define _2A00_CGC_PPLL_FREQ_MUL_21_5        (0x2A00U) /* x21.5 */
#define _2B00_CGC_PPLL_FREQ_MUL_22_0        (0x2B00U) /* x22.0 */
#define _2C00_CGC_PPLL_FREQ_MUL_22_5        (0x2C00U) /* x22.5 */
#define _2D00_CGC_PPLL_FREQ_MUL_23_0        (0x2D00U) /* x23.0 */
#define _2E00_CGC_PPLL_FREQ_MUL_23_5        (0x2E00U) /* x23.5 */
#define _2F00_CGC_PPLL_FREQ_MUL_24_0        (0x2F00U) /* x24.0 */
#define _3000_CGC_PPLL_FREQ_MUL_24_5        (0x3000U) /* x24.5 */
#define _3100_CGC_PPLL_FREQ_MUL_25_0        (0x3100U) /* x25.0 */
#define _3200_CGC_PPLL_FREQ_MUL_25_5        (0x3200U) /* x25.5 */
#define _3300_CGC_PPLL_FREQ_MUL_26_0        (0x3300U) /* x26.0 */
#define _3400_CGC_PPLL_FREQ_MUL_26_5        (0x3400U) /* x26.5 */
#define _3500_CGC_PPLL_FREQ_MUL_27_0        (0x3500U) /* x27.0 */
#define _3600_CGC_PPLL_FREQ_MUL_27_5        (0x3600U) /* x27.5 */
#define _3700_CGC_PPLL_FREQ_MUL_28_0        (0x3700U) /* x28.0 */
#define _3800_CGC_PPLL_FREQ_MUL_28_5        (0x3800U) /* x28.5 */
#define _3900_CGC_PPLL_FREQ_MUL_29_0        (0x3900U) /* x29.0 */
#define _3A00_CGC_PPLL_FREQ_MUL_29_5        (0x3A00U) /* x29.5 */
#define _3B00_CGC_PPLL_FREQ_MUL_30_0        (0x3B00U) /* x30.0 */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_CGC_Create(void);
void R_CGC_Create_UserInit(void);
/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif
