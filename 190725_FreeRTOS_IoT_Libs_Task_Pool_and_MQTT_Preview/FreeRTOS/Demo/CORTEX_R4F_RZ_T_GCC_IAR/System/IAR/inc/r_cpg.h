/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* System Name  : RZ/T1 Init program
* File Name    : r_cpg.h
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for CPG function
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : CPG setting API of RZ/T1
* Limitation   : none
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/

#ifndef _R_CPG_HEADER_
#define _R_CPG_HEADER_

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/

/*******************************************************************************
Macro definitions
*******************************************************************************/
#define CPG_CPUCLK_150_MHz (0)
#define CPG_CPUCLK_300_MHz (1)
#define CPG_CPUCLK_450_MHz (2)
#define CPG_CPUCLK_600_MHz (3)

#define CPG_PLL1_OFF (0)
#define CPG_PLL1_ON  (1)

#define CPG_SELECT_PLL0 (0)
#define CPG_SELECT_PLL1 (1)

#define CPG_CKIO_75_MHz    (0)
#define CPG_CKIO_50_MHz    (1)
#define CPG_CKIO_37_5_MHz  (2)
#define CPG_CKIO_30_MHz    (3)
#define CPG_CKIO_25_MHz    (4)
#define CPG_CKIO_21_43_MHz (5)
#define CPG_CKIO_18_75_MHz (6)

#define CPG_LOCO_ENABLE  (0x00000000)
#define CPG_LOCO_DISABLE (0x00000001)


/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/
void R_CPG_WriteEnable(void);
void R_CPG_WriteDisable(void);
void R_CPG_PLL_Wait(void);

#endif

/* End of File */
