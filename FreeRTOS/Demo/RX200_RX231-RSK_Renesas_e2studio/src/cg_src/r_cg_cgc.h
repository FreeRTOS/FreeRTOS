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
* Version      : Code Generator for RX231 V1.00.00.03 [10 Jul 2015]
* Device(s)    : R5F52318AxFP
* Tool-Chain   : CCRX
* Description  : This file implements device driver for CGC module.
* Creation Date: 2015/08/17
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
#define _0002_CGC_PLL_FREQ_DIV_4            (0x0002U) /* x1/4 */
/* Frequency Multiplication Factor Select (STC[5:0]) */
#define _0700_CGC_PLL_FREQ_MUL_4_0          (0x0700U) /* x4 */
#define _0800_CGC_PLL_FREQ_MUL_4_5          (0x0800U) /* x4.5 */
#define _0900_CGC_PLL_FREQ_MUL_5_0          (0x0900U) /* x5 */
#define _0A00_CGC_PLL_FREQ_MUL_5_5          (0x0A00U) /* x5.5 */
#define _0B00_CGC_PLL_FREQ_MUL_6_0          (0x0B00U) /* x6 */
#define _0C00_CGC_PLL_FREQ_MUL_6_5          (0x0C00U) /* x6.5 */
#define _0D00_CGC_PLL_FREQ_MUL_7_0          (0x0D00U) /* x7 */
#define _0E00_CGC_PLL_FREQ_MUL_7_5          (0x0E00U) /* x7.5 */
#define _0F00_CGC_PLL_FREQ_MUL_8_0          (0x0F00U) /* x8 */
#define _1000_CGC_PLL_FREQ_MUL_8_5          (0x1000U) /* x8.5 */
#define _1100_CGC_PLL_FREQ_MUL_9_0          (0x1100U) /* x9 */
#define _1200_CGC_PLL_FREQ_MUL_9_5          (0x1200U) /* x9.5 */
#define _1300_CGC_PLL_FREQ_MUL_10_0         (0x1300U) /* x10 */
#define _1400_CGC_PLL_FREQ_MUL_10_5         (0x1400U) /* x10.5 */
#define _1500_CGC_PLL_FREQ_MUL_11_0         (0x1500U) /* x11 */
#define _1600_CGC_PLL_FREQ_MUL_11_5         (0x1600U) /* 11.5 */
#define _1700_CGC_PLL_FREQ_MUL_12_0         (0x1700U) /* x12 */
#define _1800_CGC_PLL_FREQ_MUL_12_5         (0x1800U) /* x12.5 */
#define _1900_CGC_PLL_FREQ_MUL_13_0         (0x1900U) /* x13 */
#define _1A00_CGC_PLL_FREQ_MUL_13_5         (0x1A00U) /* x13.5 */
/*
    USB-dedicated PLL Control Register (UPLLCR)
*/
/* USB-dedicated PLL Input Frequency Division Ratio Select (UPLIDIV[1:0]) */
#define _0000_CGC_UPLL_DIV_1                (0x0000U) /* x1 */
#define _0001_CGC_UPLL_DIV_2                (0x0001U) /* x1/2 */
#define _0002_CGC_UPLL_DIV_4                (0x0002U) /* x1/4 */
/* UCLK Source USB-Dedicated PLL Select (UCKUPLLSEL) */
#define _0000_CGC_UCLK_SYSCLK               (0x0000U) /* System clock is selected as UCLK */
#define _0010_CGC_UCLK_USBPLL               (0x0010U) /* USB-dedicated PLL is selected as UCLK */
/* Frequency Multiplication Factor Select (USTC[5:0]) */
#define _0700_CGC_UPLL_MUL_4                (0x0700U) /* x4 */
#define _0B00_CGC_UPLL_MUL_6                (0x0B00U) /* x6 */
#define _0F00_CGC_UPLL_MUL_8                (0x0F00U) /* x8 */
#define _1700_CGC_UPLL_MUL_12               (0x1700U) /* x12 */

/*
    High-Speed On-Chip Oscillator Control Register 2 (HOCOCR2)
*/
/* HOCO Frequency Setting (HCFRQ[1:0]) */
#define _00_CGC_HOCO_CLK_32                 (0x00U) /* 32 MHz */
#define _03_CGC_HOCO_CLK_54                 (0x03U) /* 54 MHz */

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
    Main Clock Oscillator Wait Control Register (MOSCWTCR)
*/
/* Main Clock Oscillator Wait Time (MSTS[4:0]) */
#define _00_CGC_OSC_WAIT_CYCLE_2            (0x00U) /* Wait time = 2 cycles */
#define _01_CGC_OSC_WAIT_CYCLE_1024         (0x01U) /* Wait time = 1024 cycles */
#define _02_CGC_OSC_WAIT_CYCLE_2048         (0x02U) /* Wait time = 2048 cycles */
#define _03_CGC_OSC_WAIT_CYCLE_4096         (0x03U) /* Wait time = 4096 cycles */
#define _04_CGC_OSC_WAIT_CYCLE_8192         (0x04U) /* Wait time = 8192 cycles */
#define _05_CGC_OSC_WAIT_CYCLE_16384        (0x05U) /* Wait time = 16384 cycles */
#define _06_CGC_OSC_WAIT_CYCLE_32768        (0x06U) /* Wait time = 32768 cycles */
#define _07_CGC_OSC_WAIT_CYCLE_65536        (0x07U) /* Wait time = 65536 cycles */

/*
    Clock Output Control Register (CKOCR)
*/
/* Clock Output Source Select (CKOSEL[2:0]) */
#define _0000_CGC_CLKOUT_LOCO               (0x0000U) /* LOCO */
#define _0100_CGC_CLKOUT_HOCO               (0x0100U) /* HOCO */
#define _0200_CGC_CLKOUT_MAINCLK            (0x0200U) /* Main clock oscillator */
#define _0300_CGC_CLKOUT_SUBCLK             (0x0300U) /* Sub-clock oscillator */
#define _0400_CGC_CLKOUT_PLLCLK             (0x0400U) /* PLL clock oscillator */
/* Clock Output Division Ratio Select (CKODIV[2:0]) */
#define _0000_CGC_CLKOUT_DIV_1              (0x0000U) /* x1 */
#define _1000_CGC_CLKOUT_DIV_2              (0x1000U) /* x1/2 */
#define _2000_CGC_CLKOUT_DIV_4              (0x2000U) /* x1/4 */
#define _3000_CGC_CLKOUT_DIV_8              (0x3000U) /* x1/8 */
#define _4000_CGC_CLKOUT_DIV_16             (0x4000U) /* x1/16 */
/* Clock Output Control (CKOSTP) */
#define _0000_CGC_CLKOUT_ENABLE             (0x0000U) /* CLKOUT pin output is operating */
#define _8000_CGC_CLKOUT_DISABLE            (0x8000U) /* CLKOUT pin output is stopped (fixed at low level) */

/*
    Main Clock Oscillator Forced Oscillation Control Register (MOFCR)
*/
/* Main Oscillator Drive Capability Switch (MODRV21) */
#define _00_CGC_MAINOSC_UNDER10M            (0x00U) /* 1 MHz to 10 MHz */
#define _20_CGC_MAINOSC_OVER10M             (0x20U) /* 10 MHz to 20 MHz */
/* Main Clock Oscillator Switch (MOSEL) */
#define _00_CGC_MAINOSC_RESONATOR           (0x00U) /* Resonator */
#define _40_CGC_MAINOSC_EXTERNAL            (0x40U) /* External oscillator input */

/*
    Low-power timer control register 1 (LPTCR1)
*/
/* Low-Power Timer Clock Division Ratio Select (LPCNTPSSEL[2:0]) */
#define _01_CGC_LPT_CLK_DIV_2               (0x01U) /* x1/2 */
#define _02_CGC_LPT_CLK_DIV_4               (0x02U) /* x1/4 */
#define _03_CGC_LPT_CLK_DIV_8               (0x03U) /* x1/8 */
#define _04_CGC_LPT_CLK_DIV_16              (0x04U) /* x1/16 */
#define _05_CGC_LPT_CLK_DIV_32              (0x05U) /* x1/32 */
/* Low-Power Timer Clock Source Select (LPCNTCKSEL) */
#define _00_CGC_LPT_SOURCE_SUB              (0x00U) /* Sub-clock */
#define _10_CGC_LPT_SOURCE_IWDT             (0x10U) /* IWDT-dedicated on-chip */


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define _007B_CGC_SUBSTPWT_WAIT             (0x007BU) /* Wait time for 5 sub clock cycles */
#define _00061A81_CGC_SUBOSCWT_WAIT         (0x00061A81U) /* Wait time for sub clock stable */

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