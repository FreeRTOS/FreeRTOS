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
* File Name    : r_cg_icu.h
* Version      : Code Generator for RX71M V1.00.02.02 [28 May 2015]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : CCRX
* Description  : This file implements device driver for ICU module.
* Creation Date: 20/09/2015
***********************************************************************************************************************/
#ifndef ICU_H
#define ICU_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    Interrupt Request Enable Register 08 (IER08)
*/
/* Interrupt Priority Level Select (IPR[3:0]) */
#define _00_ICU_IRQ0_DISABLE                    (0x00U) /* IRQ0 interrupt request is disabled */
#define _01_ICU_IRQ0_ENABLE                     (0x01U) /* IRQ0 interrupt request is enabled */
#define _00_ICU_IRQ1_DISABLE                    (0x00U) /* IRQ1 interrupt request is disabled */
#define _02_ICU_IRQ1_ENABLE                     (0x02U) /* IRQ1 interrupt request is enabled */
#define _00_ICU_IRQ2_DISABLE                    (0x00U) /* IRQ2 interrupt request is disabled */
#define _04_ICU_IRQ2_ENABLE                     (0x04U) /* IRQ2 interrupt request is enabled */
#define _00_ICU_IRQ3_DISABLE                    (0x00U) /* IRQ3 interrupt request is disabled */
#define _08_ICU_IRQ3_ENABLE                     (0x08U) /* IRQ3 interrupt request is enabled */
#define _00_ICU_IRQ4_DISABLE                    (0x00U) /* IRQ4 interrupt request is disabled */
#define _10_ICU_IRQ4_ENABLE                     (0x10U) /* IRQ4 interrupt request is enabled */
#define _00_ICU_IRQ5_DISABLE                    (0x00U) /* IRQ5 interrupt request is disabled */
#define _20_ICU_IRQ5_ENABLE                     (0x20U) /* IRQ5 interrupt request is enabled */
#define _00_ICU_IRQ6_DISABLE                    (0x00U) /* IRQ6 interrupt request is disabled */
#define _40_ICU_IRQ6_ENABLE                     (0x40U) /* IRQ6 interrupt request is enabled */
#define _00_ICU_IRQ7_DISABLE                    (0x00U) /* IRQ7 interrupt request is disabled */
#define _80_ICU_IRQ7_ENABLE                     (0x80U) /* IRQ7 interrupt request is enabled */

/*
    Interrupt Request Enable Register 09 (IER09)
*/
/* Interrupt Priority Level Select (IPR[3:0]) */
#define _00_ICU_IRQ8_DISABLE                    (0x00U) /* IRQ8 interrupt request is disabled */
#define _01_ICU_IRQ8_ENABLE                     (0x01U) /* IRQ8 interrupt request is enabled */
#define _00_ICU_IRQ9_DISABLE                    (0x00U) /* IRQ9 interrupt request is disabled */
#define _02_ICU_IRQ9_ENABLE                     (0x02U) /* IRQ9 interrupt request is enabled */
#define _00_ICU_IRQ10_DISABLE                   (0x00U) /* IRQ10 interrupt request is disabled */
#define _04_ICU_IRQ10_ENABLE                    (0x04U) /* IRQ10 interrupt request is enabled */
#define _00_ICU_IRQ11_DISABLE                   (0x00U) /* IRQ11 interrupt request is disabled */
#define _08_ICU_IRQ11_ENABLE                    (0x08U) /* IRQ11 interrupt request is enabled */
#define _00_ICU_IRQ12_DISABLE                   (0x00U) /* IRQ12 interrupt request is disabled */
#define _10_ICU_IRQ12_ENABLE                    (0x10U) /* IRQ12 interrupt request is enabled */
#define _00_ICU_IRQ13_DISABLE                   (0x00U) /* IRQ13 interrupt request is disabled */
#define _20_ICU_IRQ13_ENABLE                    (0x20U) /* IRQ13 interrupt request is enabled */
#define _00_ICU_IRQ14_DISABLE                   (0x00U) /* IRQ14 interrupt request is disabled */
#define _40_ICU_IRQ14_ENABLE                    (0x40U) /* IRQ14 interrupt request is enabled */
#define _00_ICU_IRQ15_DISABLE                   (0x00U) /* IRQ15 interrupt request is disabled */
#define _80_ICU_IRQ15_ENABLE                    (0x80U) /* IRQ15 interrupt request is enabled */

/*
    Interrupt Source Priority Register n (IPRn)
*/
/* Interrupt Priority Level Select (IPR[3:0]) */
#define _00_ICU_PRIORITY_LEVEL0                 (0x00U) /* Level 0 (interrupt disabled) */
#define _01_ICU_PRIORITY_LEVEL1                 (0x01U) /* Level 1 */
#define _02_ICU_PRIORITY_LEVEL2                 (0x02U) /* Level 2 */
#define _03_ICU_PRIORITY_LEVEL3                 (0x03U) /* Level 3 */
#define _04_ICU_PRIORITY_LEVEL4                 (0x04U) /* Level 4 */
#define _05_ICU_PRIORITY_LEVEL5                 (0x05U) /* Level 5 */
#define _06_ICU_PRIORITY_LEVEL6                 (0x06U) /* Level 6 */
#define _07_ICU_PRIORITY_LEVEL7                 (0x07U) /* Level 7 */
#define _08_ICU_PRIORITY_LEVEL8                 (0x08U) /* Level 8 */
#define _09_ICU_PRIORITY_LEVEL9                 (0x09U) /* Level 9 */
#define _0A_ICU_PRIORITY_LEVEL10                (0x0AU) /* Level 10 */
#define _0B_ICU_PRIORITY_LEVEL11                (0x0BU) /* Level 11 */
#define _0C_ICU_PRIORITY_LEVEL12                (0x0CU) /* Level 12 */
#define _0D_ICU_PRIORITY_LEVEL13                (0x0DU) /* Level 13 */
#define _0E_ICU_PRIORITY_LEVEL14                (0x0EU) /* Level 14 */
#define _0F_ICU_PRIORITY_LEVEL15                (0x0FU) /* Level 15 (highest) */

/*
    Fast Interrupt Set Register (FIR)
*/
/* Fast Interrupt Enable (FIEN) */
#define _0000_ICU_FAST_INTERRUPT_DISABLE        (0x0000U) /* Fast interrupt is disabled */
#define _8000_ICU_FAST_INTERRUPT_ENABLE         (0x8000U) /* Fast interrupt is enabled */

/*
    IRQ Control Register i (IRQCRi) (i = 0 to 7)
*/
/* IRQ Detection Sense Select (IRQMD[1:0]) */
#define _00_ICU_IRQ_EDGE_LOW_LEVEL              (0x00U) /* Low level */
#define _04_ICU_IRQ_EDGE_FALLING                (0x04U) /* Falling edge */
#define _08_ICU_IRQ_EDGE_RISING                 (0x08U) /* Rising edge */
#define _0C_ICU_IRQ_EDGE_BOTH                   (0x0CU) /* Rising and falling edge */

/*
    IRQ Pin Digital Filter Enable Register 0 (IRQFLTE0)
*/
/* Digital Filter Enable (FLTEN0n) */
#define _00_ICU_IRQn_FILTER_DISABLE             (0x00U) /* IRQn digital filter is disabled */
#define _01_ICU_IRQ0_FILTER_ENABLE              (0x01U) /* IRQ0 digital filter is enabled */
#define _02_ICU_IRQ1_FILTER_ENABLE              (0x02U) /* IRQ1 digital filter is enabled */
#define _04_ICU_IRQ2_FILTER_ENABLE              (0x04U) /* IRQ2 digital filter is enabled */
#define _08_ICU_IRQ3_FILTER_ENABLE              (0x08U) /* IRQ3 digital filter is enabled */
#define _10_ICU_IRQ4_FILTER_ENABLE              (0x10U) /* IRQ4 digital filter is enabled */
#define _20_ICU_IRQ5_FILTER_ENABLE              (0x20U) /* IRQ5 digital filter is enabled */
#define _40_ICU_IRQ6_FILTER_ENABLE              (0x40U) /* IRQ6 digital filter is enabled */
#define _80_ICU_IRQ7_FILTER_ENABLE              (0x80U) /* IRQ7 digital filter is enabled */

/*
    IRQ Pin Digital Filter Enable Register 1 (IRQFLTE1)
*/
/* Digital Filter Enable (FLTEN8~15) */
#define _01_ICU_IRQ8_FILTER_ENABLE              (0x01U) /* IRQ8 digital filter is enabled */
#define _02_ICU_IRQ9_FILTER_ENABLE              (0x02U) /* IRQ9 digital filter is enabled */
#define _04_ICU_IRQ10_FILTER_ENABLE             (0x04U) /* IRQ10 digital filter is enabled */
#define _08_ICU_IRQ11_FILTER_ENABLE             (0x08U) /* IRQ11 digital filter is enabled */
#define _10_ICU_IRQ12_FILTER_ENABLE             (0x10U) /* IRQ12 digital filter is enabled */
#define _20_ICU_IRQ13_FILTER_ENABLE             (0x20U) /* IRQ13 digital filter is enabled */
#define _40_ICU_IRQ14_FILTER_ENABLE             (0x40U) /* IRQ14 digital filter is enabled */
#define _80_ICU_IRQ15_FILTER_ENABLE             (0x80U) /* IRQ15 digital filter is enabled */

/*
    IRQ Pin Digital Filter Setting Register 0 (IRQFLTC0)
*/
/* IRQn Digital Filter Sampling Clock (FCLKSELn) */
#define _0000_ICU_IRQ0_FILTER_PCLK              (0x0000U) /* IRQ0 sample clock is run at every PCLK cycle */
#define _0001_ICU_IRQ0_FILTER_PCLK_8            (0x0001U) /* IRQ0 sample clock is run at every PCLK/8 cycle */
#define _0002_ICU_IRQ0_FILTER_PCLK_32           (0x0002U) /* IRQ0 sample clock is run at every PCLK/32 cycle */
#define _0003_ICU_IRQ0_FILTER_PCLK_64           (0x0003U) /* IRQ0 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ1_FILTER_PCLK              (0x0000U) /* IRQ1 sample clock is run at every PCLK cycle */
#define _0004_ICU_IRQ1_FILTER_PCLK_8            (0x0004U) /* IRQ1 sample clock is run at every PCLK/8 cycle */
#define _0008_ICU_IRQ1_FILTER_PCLK_32           (0x0008U) /* IRQ1 sample clock is run at every PCLK/32 cycle */
#define _000C_ICU_IRQ1_FILTER_PCLK_64           (0x000CU) /* IRQ1 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ2_FILTER_PCLK              (0x0000U) /* IRQ2 sample clock is run at every PCLK cycle */
#define _0010_ICU_IRQ2_FILTER_PCLK_8            (0x0010U) /* IRQ2 sample clock is run at every PCLK/8 cycle */
#define _0020_ICU_IRQ2_FILTER_PCLK_32           (0x0020U) /* IRQ2 sample clock is run at every PCLK/32 cycle */
#define _0030_ICU_IRQ2_FILTER_PCLK_64           (0x0030U) /* IRQ2 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ3_FILTER_PCLK              (0x0000U) /* IRQ3 sample clock is run at every PCLK cycle */
#define _0040_ICU_IRQ3_FILTER_PCLK_8            (0x0040U) /* IRQ3 sample clock is run at every PCLK/8 cycle */
#define _0080_ICU_IRQ3_FILTER_PCLK_32           (0x0080U) /* IRQ3 sample clock is run at every PCLK/32 cycle */
#define _00C0_ICU_IRQ3_FILTER_PCLK_64           (0x00C0U) /* IRQ3 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ4_FILTER_PCLK              (0x0000U) /* IRQ4 sample clock is run at every PCLK cycle */
#define _0100_ICU_IRQ4_FILTER_PCLK_8            (0x0100U) /* IRQ4 sample clock is run at every PCLK/8 cycle */
#define _0200_ICU_IRQ4_FILTER_PCLK_32           (0x0200U) /* IRQ4 sample clock is run at every PCLK/32 cycle */
#define _0300_ICU_IRQ4_FILTER_PCLK_64           (0x0300U) /* IRQ4 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ5_FILTER_PCLK              (0x0000U) /* IRQ5 sample clock is run at every PCLK cycle */
#define _0400_ICU_IRQ5_FILTER_PCLK_8            (0x0400U) /* IRQ5 sample clock is run at every PCLK/8 cycle */
#define _0800_ICU_IRQ5_FILTER_PCLK_32           (0x0800U) /* IRQ5 sample clock is run at every PCLK/32 cycle */
#define _0C00_ICU_IRQ5_FILTER_PCLK_64           (0x0C00U) /* IRQ5 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ6_FILTER_PCLK              (0x0000U) /* IRQ6 sample clock is run at every PCLK cycle */
#define _1000_ICU_IRQ6_FILTER_PCLK_8            (0x1000U) /* IRQ6 sample clock is run at every PCLK/8 cycle */
#define _2000_ICU_IRQ6_FILTER_PCLK_32           (0x2000U) /* IRQ6 sample clock is run at every PCLK/32 cycle */
#define _3000_ICU_IRQ6_FILTER_PCLK_64           (0x3000U) /* IRQ6 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ7_FILTER_PCLK              (0x0000U) /* IRQ7 sample clock is run at every PCLK cycle */
#define _4000_ICU_IRQ7_FILTER_PCLK_8            (0x4000U) /* IRQ7 sample clock is run at every PCLK/8 cycle */
#define _8000_ICU_IRQ7_FILTER_PCLK_32           (0x8000U) /* IRQ7 sample clock is run at every PCLK/32 cycle */
#define _C000_ICU_IRQ7_FILTER_PCLK_64           (0xC000U) /* IRQ7 sample clock is run at every PCLK/64 cycle */

/*
    IRQ Pin Digital Filter Setting Register 0 (IRQFLTC1)
*/
/* IRQn Digital Filter Sampling Clock (FCLKSEL8~15) */
#define _0000_ICU_IRQ8_FILTER_PCLK              (0x0000U) /* IRQ8 sample clock is run at every PCLK cycle */
#define _0001_ICU_IRQ8_FILTER_PCLK_8            (0x0001U) /* IRQ8 sample clock is run at every PCLK/8 cycle */
#define _0002_ICU_IRQ8_FILTER_PCLK_32           (0x0002U) /* IRQ8 sample clock is run at every PCLK/32 cycle */
#define _0003_ICU_IRQ8_FILTER_PCLK_64           (0x0003U) /* IRQ8 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ9_FILTER_PCLK              (0x0000U) /* IRQ9 sample clock is run at every PCLK cycle */
#define _0004_ICU_IRQ9_FILTER_PCLK_8            (0x0004U) /* IRQ9 sample clock is run at every PCLK/8 cycle */
#define _0008_ICU_IRQ9_FILTER_PCLK_32           (0x0008U) /* IRQ9 sample clock is run at every PCLK/32 cycle */
#define _000C_ICU_IRQ9_FILTER_PCLK_64           (0x000CU) /* IRQ9 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ10_FILTER_PCLK             (0x0000U) /* IRQ10 sample clock is run at every PCLK cycle */
#define _0010_ICU_IRQ10_FILTER_PCLK_8           (0x0010U) /* IRQ10 sample clock is run at every PCLK/8 cycle */
#define _0020_ICU_IRQ10_FILTER_PCLK_32          (0x0020U) /* IRQ10 sample clock is run at every PCLK/32 cycle */
#define _0030_ICU_IRQ10_FILTER_PCLK_64          (0x0030U) /* IRQ10 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ11_FILTER_PCLK             (0x0000U) /* IRQ11 sample clock is run at every PCLK cycle */
#define _0040_ICU_IRQ11_FILTER_PCLK_8           (0x0040U) /* IRQ11 sample clock is run at every PCLK/8 cycle */
#define _0080_ICU_IRQ11_FILTER_PCLK_32          (0x0080U) /* IRQ11 sample clock is run at every PCLK/32 cycle */
#define _00C0_ICU_IRQ11_FILTER_PCLK_64          (0x00C0U) /* IRQ11 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ12_FILTER_PCLK             (0x0000U) /* IRQ12 sample clock is run at every PCLK cycle */
#define _0100_ICU_IRQ12_FILTER_PCLK_8           (0x0100U) /* IRQ12 sample clock is run at every PCLK/8 cycle */
#define _0200_ICU_IRQ12_FILTER_PCLK_32          (0x0200U) /* IRQ12 sample clock is run at every PCLK/32 cycle */
#define _0300_ICU_IRQ12_FILTER_PCLK_64          (0x0300U) /* IRQ12 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ13_FILTER_PCLK             (0x0000U) /* IRQ13 sample clock is run at every PCLK cycle */
#define _0400_ICU_IRQ13_FILTER_PCLK_8           (0x0400U) /* IRQ13 sample clock is run at every PCLK/8 cycle */
#define _0800_ICU_IRQ13_FILTER_PCLK_32          (0x0800U) /* IRQ13 sample clock is run at every PCLK/32 cycle */
#define _0C00_ICU_IRQ13_FILTER_PCLK_64          (0x0C00U) /* IRQ13 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ14_FILTER_PCLK             (0x0000U) /* IRQ14 sample clock is run at every PCLK cycle */
#define _1000_ICU_IRQ14_FILTER_PCLK_8           (0x1000U) /* IRQ14 sample clock is run at every PCLK/8 cycle */
#define _2000_ICU_IRQ14_FILTER_PCLK_32          (0x2000U) /* IRQ14 sample clock is run at every PCLK/32 cycle */
#define _3000_ICU_IRQ14_FILTER_PCLK_64          (0x3000U) /* IRQ14 sample clock is run at every PCLK/64 cycle */
#define _0000_ICU_IRQ15_FILTER_PCLK             (0x0000U) /* IRQ15 sample clock is run at every PCLK cycle */
#define _4000_ICU_IRQ15_FILTER_PCLK_8           (0x4000U) /* IRQ15 sample clock is run at every PCLK/8 cycle */
#define _8000_ICU_IRQ15_FILTER_PCLK_32          (0x8000U) /* IRQ15 sample clock is run at every PCLK/32 cycle */
#define _C000_ICU_IRQ15_FILTER_PCLK_64          (0xC000U) /* IRQ15 sample clock is run at every PCLK/64 cycle */


/*
    NMI Pin Interrupt Control Register (NMICR)
*/
/* NMI Digital Filter Sampling Clock (NMIMD) */
#define _00_ICU_NMI_EDGE_FALLING                (0x00U) /* Falling edge */
#define _08_ICU_NMI_EDGE_RISING                 (0x08U) /* Rising edge */

/*
    NMI Pin Digital Filter Setting Register (NMIFLTC)
*/
/* NMI Digital Filter Sampling Clock (NFCLKSEL[1:0]) */
#define _00_ICU_NMI_FILTER_PCLK                 (0x00U) /* NMI sample clock is run at every PCLK cycle */
#define _01_ICU_NMI_FILTER_PCLK_8               (0x01U) /* NMI sample clock is run at every PCLK/8 cycle */
#define _02_ICU_NMI_FILTER_PCLK_32              (0x02U) /* NMI sample clock is run at every PCLK/32 cycle */
#define _03_ICU_NMI_FILTER_PCLK_64              (0x03U) /* NMI sample clock is run at every PCLK/64 cycle */

/*
    EXDMAC Activation Peripheral Interrupt Select Register (SELEXDR)
*/
/* EXDMAC0 Activation Peripheral Interrupt Select (SELEXD0) */
#define _00_ICU_EXDMAC0_SLIBR144                (0x00U) /* Interrupt B selected in SLIBR144 activates EXDMAC0 */
#define _01_ICU_EXDMAC0_SLIAR208                (0x01U) /* Interrupt B selected in SLIAR208 activates EXDMAC0 */
/* EXDMAC1 Activation Peripheral Interrupt Select (SELEXD1) */
#define _00_ICU_EXDMAC1_SLIBR145                (0x00U) /* Interrupt B selected in SLIBR145 activates EXDMAC1 */
#define _02_ICU_EXDMAC1_SLIAR209                (0x02U) /* Interrupt B selected in SLIAR209 activates EXDMAC1 */


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_ICU_Create(void);
void R_ICU_IRQ2_Start(void);
void R_ICU_IRQ2_Stop(void);
void R_ICU_IRQ5_Start(void);
void R_ICU_IRQ5_Stop(void);

/* Start user code for function. Do not edit comment generated here */

/* Function prototypes for detecting and setting the edge trigger of ICU_IRQ */
uint8_t R_ICU_IRQIsFallingEdge(const uint8_t irq_no);
void R_ICU_IRQSetFallingEdge(const uint8_t irq_no, const uint8_t set_f_edge);
void R_ICU_IRQSetRisingEdge(const uint8_t irq_no, const uint8_t set_r_edge);

/* End user code. Do not edit comment generated here */
#endif