/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
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
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_cgc.h
* Version      : Code Generator for RX71M V1.00.02.02 [28 May 2015]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : CCRX
* Description  : This file implements device driver for CGC module.
* Creation Date: 20/09/2015
***********************************************************************************************************************/
#ifndef CGC_H
#define CGC_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    System Clock Control Register (SCKCR)
*/
/* Peripheral Module Clock D (PCLKD) */
#define _00000000_CGC_PCLKD_DIV_1           (0x00000000UL) /* x1 */
#define _00000001_CGC_PCLKD_DIV_2           (0x00000001UL) /* x1/2 */
#define _00000002_CGC_PCLKD_DIV_4           (0x00000002UL) /* x1/4 */
#define _00000003_CGC_PCLKD_DIV_8           (0x00000003UL) /* x1/8 */
#define _00000004_CGC_PCLKD_DIV_16          (0x00000004UL) /* x1/16 */
#define _00000005_CGC_PCLKD_DIV_32          (0x00000005UL) /* x1/32 */
#define _00000006_CGC_PCLKD_DIV_64          (0x00000006UL) /* x1/64 */
/* Peripheral Module Clock C (PCLKC) */
#define _00000000_CGC_PCLKC_DIV_1           (0x00000000UL) /* x1 */
#define _00000010_CGC_PCLKC_DIV_2           (0x00000010UL) /* x1/2 */
#define _00000020_CGC_PCLKC_DIV_4           (0x00000020UL) /* x1/4 */
#define _00000030_CGC_PCLKC_DIV_8           (0x00000030UL) /* x1/8 */
#define _00000040_CGC_PCLKC_DIV_16          (0x00000040UL) /* x1/16 */
#define _00000050_CGC_PCLKC_DIV_32          (0x00000050UL) /* x1/32 */
#define _00000060_CGC_PCLKC_DIV_64          (0x00000060UL) /* x1/64 */
/* Peripheral Module Clock B (PCLKB) */
#define _00000000_CGC_PCLKB_DIV_1           (0x00000000UL) /* x1 */
#define _00000100_CGC_PCLKB_DIV_2           (0x00000100UL) /* x1/2 */
#define _00000200_CGC_PCLKB_DIV_4           (0x00000200UL) /* x1/4 */
#define _00000300_CGC_PCLKB_DIV_8           (0x00000300UL) /* x1/8 */
#define _00000400_CGC_PCLKB_DIV_16          (0x00000400UL) /* x1/16 */
#define _00000500_CGC_PCLKB_DIV_32          (0x00000500UL) /* x1/32 */
#define _00000600_CGC_PCLKB_DIV_64          (0x00000600UL) /* x1/64 */
/* Peripheral Module Clock A (PCLKA) */
#define _00000000_CGC_PCLKA_DIV_1           (0x00000000UL) /* x1 */
#define _00001000_CGC_PCLKA_DIV_2           (0x00001000UL) /* x1/2 */
#define _00002000_CGC_PCLKA_DIV_4           (0x00002000UL) /* x1/4 */
#define _00003000_CGC_PCLKA_DIV_8           (0x00003000UL) /* x1/8 */
#define _00004000_CGC_PCLKA_DIV_16          (0x00004000UL) /* x1/16 */
#define _00005000_CGC_PCLKA_DIV_32          (0x00005000UL) /* x1/32 */
#define _00006000_CGC_PCLKA_DIV_64          (0x00006000UL) /* x1/64 */
/* External Bus Clock (BCLK) */
#define _00000000_CGC_BCLK_DIV_1            (0x00000000UL) /* x1 */
#define _00010000_CGC_BCLK_DIV_2            (0x00010000UL) /* x1/2 */
#define _00020000_CGC_BCLK_DIV_4            (0x00020000UL) /* x1/4 */
#define _00030000_CGC_BCLK_DIV_8            (0x00030000UL) /* x1/8 */
#define _00040000_CGC_BCLK_DIV_16           (0x00040000UL) /* x1/16 */
#define _00050000_CGC_BCLK_DIV_32           (0x00050000UL) /* x1/32 */
#define _00060000_CGC_BCLK_DIV_64           (0x00060000UL) /* x1/64 */
/* System Clock (ICLK) */
#define _00000000_CGC_ICLK_DIV_1            (0x00000000UL) /* x1 */
#define _01000000_CGC_ICLK_DIV_2            (0x01000000UL) /* x1/2 */
#define _02000000_CGC_ICLK_DIV_4            (0x02000000UL) /* x1/4 */
#define _03000000_CGC_ICLK_DIV_8            (0x03000000UL) /* x1/8 */
#define _04000000_CGC_ICLK_DIV_16           (0x04000000UL) /* x1/16 */
#define _05000000_CGC_ICLK_DIV_32           (0x05000000UL) /* x1/32 */
#define _06000000_CGC_ICLK_DIV_64           (0x06000000UL) /* x1/64 */
/* System Clock (FCLK) */
#define _00000000_CGC_FCLK_DIV_1            (0x00000000UL) /* x1 */
#define _10000000_CGC_FCLK_DIV_2            (0x10000000UL) /* x1/2 */
#define _20000000_CGC_FCLK_DIV_4            (0x20000000UL) /* x1/4 */
#define _30000000_CGC_FCLK_DIV_8            (0x30000000UL) /* x1/8 */
#define _40000000_CGC_FCLK_DIV_16           (0x40000000UL) /* x1/16 */
#define _50000000_CGC_FCLK_DIV_32           (0x50000000UL) /* x1/32 */
#define _60000000_CGC_FCLK_DIV_64           (0x60000000UL) /* x1/64 */

/*
    System Clock Control Register 2 (SCKCR2)
*/
#define _0010_CGC_UCLK_DIV_1                (0x0010U) /* x1/2 */
#define _0020_CGC_UCLK_DIV_3                (0x0020U) /* x1/3 */
#define _0030_CGC_UCLK_DIV_4                (0x0030U) /* x1/4 */
#define _0040_CGC_UCLK_DIV_5                (0x0040U) /* x1/5 */
#define _0001_SCKCR2_BIT0                   (0x0001U) /* RESERVE BIT0 */

/*
    System Clock Control Register 3 (SCKCR3)
*/
#define _0000_CGC_CLOCKSOURCE_LOCO          (0x0000U) /* LOCO */
#define _0100_CGC_CLOCKSOURCE_HOCO          (0x0100U) /* HOCO */
#define _0200_CGC_CLOCKSOURCE_MAINCLK       (0x0200U) /* Main clock oscillator */
#define _0300_CGC_CLOCKSOURCE_SUBCLK        (0x0300U) /* Sub-clock oscillator */
#define _0400_CGC_CLOCKSOURCE_PLL           (0x0400U) /* PLL circuit */

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
    Oscillation Stop Detection Control Register (OSTDCR)
*/
/* Oscillation Stop Detection Interrupt Enable (OSTDIE) */
#define _00_CGC_OSC_STOP_INT_DISABLE        (0x00U) /* The oscillation stop detection interrupt is disabled */
#define _01_CGC_OSC_STOP_INT_ENABLE         (0x01U) /* The oscillation stop detection interrupt is enabled */
/* Oscillation Stop Detection Function Enable (OSTDE) */
#define _00_CGC_OSC_STOP_DISABLE            (0x00U) /* Oscillation stop detection function is disabled */
#define _80_CGC_OSC_STOP_ENABLE             (0x80U) /* Oscillation stop detection function is enabled */

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
/* Main Oscillator Drive Capability 2 Switching (MODRV2[1:0]) */
#define _00_CGC_MAINOSC_UNDER24M            (0x00U) /* 20.1 to 24 MHz */
#define _10_CGC_MAINOSC_UNDER20M            (0x10U) /* 16.1 to 20 MHz */
#define _20_CGC_MAINOSC_UNDER16M            (0x20U) /* 8.1 to 16 MHz */
#define _30_CGC_MAINOSC_EQUATE8M            (0x30U) /* 8 MHz */
/* Main Clock Oscillator Switch (MOSEL) */
#define _00_CGC_MAINOSC_RESONATOR           (0x00U) /* Resonator */
#define _40_CGC_MAINOSC_EXTERNAL            (0x40U) /* External oscillator input */

/*
    RTC Control Register 4 (RCR4)
*/
/* Count source select */
#define _00_RTC_SOURCE_SELECT_SUB           (0x00U) /* Select sub-clock oscillator */
#define _01_RTC_SOURCE_SELECT_MAIN_FORCED   (0x01U) /* Select main clock oscillator */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define _5C_CGC_MOSCWTCR_VALUE              (0x5CU) /* Main Clock Oscillator Wait Time */

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_CGC_Create(void);

/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif