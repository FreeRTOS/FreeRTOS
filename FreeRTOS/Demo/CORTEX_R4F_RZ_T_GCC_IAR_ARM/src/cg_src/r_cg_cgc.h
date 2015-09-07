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
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for CGC module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef CGC_H
#define CGC_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    System Clock Control Register (SCKCR)
*/
/* Peripheral Module Clock G (PCLKG) */
#define _CGC_PCLKG_0                  (0x00000000UL) /* 60 MHz */
#define _CGC_PCLKG_1                  (0x00000001UL) /* 30 MHz */
#define _CGC_PCLKG_2                  (0x00000002UL) /* 15 MHz */
#define _CGC_PCLKG_3                  (0x00000003UL) /* 7.5 MHz */
/* Peripheral Module Clock F (PCLKF) */
#define _CGC_PCLKF_0                  (0x00000000UL) /* 60 MHz */
#define _CGC_PCLKF_1                  (0x00000004UL) /* 30 MHz */
#define _CGC_PCLKF_2                  (0x00000008UL) /* 15 MHz */
#define _CGC_PCLKF_3                  (0x0000000CUL) /* 7.5 MHz */
/* Peripheral Module Clock E (PCLKE) */
#define _CGC_PCLKE_0                  (0x00000000UL) /* 75 MHz */
#define _CGC_PCLKE_1                  (0x00000010UL) /* 37.5 MHz */
#define _CGC_PCLKE_2                  (0x00000020UL) /* 18.75 MHz */
/* External Bus Clock (CKIO) */
#define _CGC_CKIO_0                   (0x00000000UL) /* 75 MHz */
#define _CGC_CKIO_1                   (0x00000100UL) /* 50 MHz */
#define _CGC_CKIO_2                   (0x00000200UL) /* 37.5 MHz */
#define _CGC_CKIO_3                   (0x00000300UL) /* 30 MHz */
#define _CGC_CKIO_4                   (0x00000400UL) /* 25 MHz */
#define _CGC_CKIO_5                   (0x00000500UL) /* 21.43 MHz */
#define _CGC_CKIO_6                   (0x00000600UL) /* 18.75 MHz */
/* Ether Clock E  (ETCLKE) */
#define _CGC_ETCKE_0                  (0x00000000UL) /* 25 MHz */
#define _CGC_ETCKE_1                  (0x00001000UL) /* 50 MHz */
#define _CGC_ETCKE_2                  (0x00003000UL) /* 25 MHz */
/* Ether Clock D  (ETCLKD) */
#define _CGC_ETCKD_0                  (0x00000000UL) /* 12.5 MHz */
#define _CGC_ETCKD_1                  (0x00004000UL) /* 6.25 MHz */
#define _CGC_ETCKD_2                  (0x00008000UL) /* 3.125 MHz */
#define _CGC_ETCKD_3                  (0x0000C000UL) /* 1.563 MHz */
/* High-Speed Serial Clock (SERICLK) */
#define _CGC_SERICLK_0                (0x00000000UL) /* 150 MHz */
#define _CGC_SERICLK_1                (0x00010000UL) /* 120 MHz */
/* USB Clock (USBMCLK) */
#define _CGC_UCK_0                    (0x00000000UL) /* 50 MHz */
#define _CGC_UCK_1                    (0x00020000UL) /* 24 MHz */
/* Trace Interface Clock (TCLK) */
#define _CGC_TCLK_0                   (0x00000000UL) /* 150 MHz */
#define _CGC_TCLK_1                   (0x00100000UL) /* 75 MHz */

/*
    System Clock Control Register 2 (SCKCR2)
*/
#define _CGC_SKSEL0_PLL0              (0x00000000UL) /* PLL0 */
#define _CGC_SKSEL0_PLL1              (0x00000001UL) /* PLL1 */

/*
    Delta-Sigma Interface Clock Control Register (DSCR)
*/
#define _CGC_DSSEL0_SLAVE             (0x00000000UL) /* Supplied from outside the LSI (slave operation) */
#define _CGC_DSSEL0_MASTER            (0x00000001UL) /* Supplied from CGC (master operation) */
#define _CGC_DSCLK0_0                 (0x00000000UL) /* 25 MHz */
#define _CGC_DSCLK0_1                 (0x00000002UL) /* 18.75 MHz */
#define _CGC_DSCLK0_2                 (0x00000004UL) /* 12.5 MHz */
#define _CGC_DSCLK0_3                 (0x00000006UL) /* 9.375 MHz */
#define _CGC_DSCLK0_4                 (0x00000008UL) /* 6.25 MHz */
#define _CGC_DSCLK0_POL_NORMAL        (0x00000000UL) /* Polarity not inverted (master and slave operation) */
#define _CGC_DSCLK0_POL_INVERT        (0x00000010UL) /* Polarity inverted (master and slave operation) */
#define _CGC_DSCLK0_SLAVE_MCLK0_2     (0x00000000UL) /* Clock input to MCLK0,MCLK1,MCLK2 pins are used */
#define _CGC_DSCLK0_SLAVE_MCLK0       (0x00000020UL) /* Clock input to MCLK0 pin is used */
#define _CGC_DSSEL1_SLAVE             (0x00000000UL) /* Supplied from outside the LSI (slave operation) */
#define _CGC_DSSEL1_MASTER            (0x00010000UL) /* Supplied from CGC (master operation) */
#define _CGC_DSCLK1_0                 (0x00000000UL) /* 25 MHz */
#define _CGC_DSCLK1_1                 (0x00020000UL) /* 18.75 MHz */
#define _CGC_DSCLK1_2                 (0x00040000UL) /* 12.5 MHz */
#define _CGC_DSCLK1_3                 (0x00060000UL) /* 9.375 MHz */
#define _CGC_DSCLK1_4                 (0x00080000UL) /* 6.25 MHz */
#define _CGC_DSCLK1_POL_NORMAL        (0x00000000UL) /* Polarity not inverted (master and slave operation) */
#define _CGC_DSCLK1_POL_INVERT        (0x00100000UL) /* Polarity inverted (master and slave operation) */

/*
    PLL1 Control Register (PLL1CR)
*/
#define _CGC_PLL1_CPUCKSEL_150        (0x00U) /* 150 MHz */
#define _CGC_PLL1_CPUCKSEL_300        (0x01U) /* 300 MHz */
#define _CGC_PLL1_CPUCKSEL_450        (0x02U) /* 450 MHz */
#define _CGC_PLL1_CPUCKSEL_600        (0x03U) /* 600 MHz */

/*
    PLL1 Control Register 2 (PLL1CR2)
*/
#define _CGC_PLL1_DISABLE             (0x00000000UL) /* PLL1 stops */
#define _CGC_PLL1_ENABLE              (0x00000001UL) /* PLL1 runs */

/*
    Low-Speed On-Chip Oscillator Control Register (LOCOCR)
*/
#define _CGC_LOCO_RUN                 (0x00000000UL) /* LOCO Run */
#define _CGC_LOCO_STOP                (0x00000001UL) /* LOCO Stop */

/*
    Oscillation Stop Detection Control Register (OSTDCR)
*/
/* Oscillation Stop Detection Interrupt Enable (OSTDIE) */
#define _CGC_OSC_STOP_DET_INT_DISABLE (0x00000000UL) /* Stop detection interrupt is disabled */
#define _CGC_OSC_STOP_DET_INT_ENABLE  (0x00000001UL) /* Stop detection interrupt is enabled */
/* Oscillation Stop Detection Function Enable (OSTDE) */
#define _CGC_OSC_STOP_DET_DISABLE     (0x00000000UL) /* Oscillation stop detection function is disabled */
#define _CGC_OSC_STOP_DET_ENABLE      (0x00000080UL) /* Oscillation stop detection function is enabled */

/*
    ECM Non-maskable Interrupt Configuration Register 0 (ECMNMICFG0)    
*/
#define _ECM_NMI_OSC_STOP_DISABLE     (0x00000000UL) /* Stop detection NMI interrupt is disabled */
#define _ECM_NMI_OSC_STOP_ENABLE      (0x00080000UL) /* Stop detection NMI interrupt is enabled */

/*
    ECM Maskable Interrupt Configuration Register 0 (ECMMICFG0)
*/
#define _ECM_MI_OSC_STOP_DISABLE      (0x00000000UL) /* Stop detection Maskable interrupt is disabled */
#define _ECM_MI_OSC_STOP_ENABLE       (0x00080000UL) /* Stop detection Maskable interrupt is enabled */

/*
    Debugging Interface Control Register (DBGIFCNT)
*/
#define _SWV_SEL_NOOUTPUT             (0x00000000UL) /* SWV output is not output */
#define _SWV_SEL_TDO                  (0x00000001UL) /* SWV output is output from the TDO pin */
#define _SWV_SEL_TRACEDATA0           (0x00000002UL) /* SWV output is output from the TRACEDATA0 pin */
#define _SWV_SEL_TRACECTL             (0x00000003UL) /* SWV output is output from the TRACECTL pin */


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define _CGC_PLL_WAIT_CYCLE           (0x1D4CU) /* Wait 100us when switch clock source in PLL0 and PLL1 */
#define _CGC_LOCO_WAIT_CYCLE          (0x0BB8U) /* Wait 40us for LOCO oscillation stabilization */    

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_CGC_Create(void);

/* Start user code for function. Do not edit comment generated here */

void R_CPG_PLLWait(void);
void R_CPG_WriteEnable(void);
void R_CPG_WriteDisable(void);

#define CPG_CPUCLK_150_MHz (0)
#define CPG_CPUCLK_300_MHz (1)
#define CPG_CPUCLK_450_MHz (2)
#define CPG_CPUCLK_600_MHz (3)

#define CPG_PLL1_OFF       (0)
#define CPG_PLL1_ON        (1)

#define CPG_SELECT_PLL0    (0)
#define CPG_SELECT_PLL1    (1)

#define CPG_CKIO_75_MHz    (0)
#define CPG_CKIO_50_MHz    (1)
#define CPG_CKIO_37_5_MHz  (2)
#define CPG_CKIO_30_MHz    (3)
#define CPG_CKIO_25_MHz    (4)
#define CPG_CKIO_21_43_MHz (5)
#define CPG_CKIO_18_75_MHz (6)

#define CPG_LOCO_ENABLE    (0x00000000)
#define CPG_LOCO_DISABLE   (0x00000001)

/* End user code. Do not edit comment generated here */
#endif