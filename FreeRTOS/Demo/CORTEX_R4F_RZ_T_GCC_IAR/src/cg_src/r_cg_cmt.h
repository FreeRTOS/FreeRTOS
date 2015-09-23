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
* File Name    : r_cg_cmt.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for CMT module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef CMT_H
#define CMT_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    Compare Match Timer Control Register (CMCR)
*/
/* Clock Select (CKS[1:0]) */
#define _CMT_CMCR_CKS_PCLK8                     (0x0000U) /* PCLK/8 */
#define _CMT_CMCR_CKS_PCLK32                    (0x0001U) /* PCLK/32 */
#define _CMT_CMCR_CKS_PCLK128                   (0x0002U) /* PCLK/128 */
#define _CMT_CMCR_CKS_PCLK512                   (0x0003U) /* PCLK/512 */
/* Compare Match Interrupt Enable (CMIE) */
#define _CMT_CMCR_CMIE_DISABLE                  (0x0000U) /* Compare match interrupt (CMIn) disabled */
#define _CMT_CMCR_CMIE_ENABLE                   (0x0040U) /* Compare match interrupt (CMIn) enabled */

/*
    Interrupt Priority Level Store Register n (PRLn)
*/
/* Interrupt Priority Level Store (PRL[3:0]) */
#define _CMT_PRIORITY_LEVEL0                    (0x00000000UL) /* Level 0 (highest) */
#define _CMT_PRIORITY_LEVEL1                    (0x00000001UL) /* Level 1 */
#define _CMT_PRIORITY_LEVEL2                    (0x00000002UL) /* Level 2 */
#define _CMT_PRIORITY_LEVEL3                    (0x00000003UL) /* Level 3 */
#define _CMT_PRIORITY_LEVEL4                    (0x00000004UL) /* Level 4 */
#define _CMT_PRIORITY_LEVEL5                    (0x00000005UL) /* Level 5 */
#define _CMT_PRIORITY_LEVEL6                    (0x00000006UL) /* Level 6 */
#define _CMT_PRIORITY_LEVEL7                    (0x00000007UL) /* Level 7 */
#define _CMT_PRIORITY_LEVEL8                    (0x00000008UL) /* Level 8 */
#define _CMT_PRIORITY_LEVEL9                    (0x00000009UL) /* Level 9 */
#define _CMT_PRIORITY_LEVEL10                   (0x0000000AUL) /* Level 10 */
#define _CMT_PRIORITY_LEVEL11                   (0x0000000BUL) /* Level 11 */
#define _CMT_PRIORITY_LEVEL12                   (0x0000000CUL) /* Level 12 */
#define _CMT_PRIORITY_LEVEL13                   (0x0000000DUL) /* Level 13 */
#define _CMT_PRIORITY_LEVEL14                   (0x0000000EUL) /* Level 14 */
#define _CMT_PRIORITY_LEVEL15                   (0x0000000FUL) /* Level 15 */
#define _CMT_PRIORITY_LEVEL16                   (0x00000000UL) /* Level 16 */
#define _CMT_PRIORITY_LEVEL17                   (0x00000001UL) /* Level 17 */
#define _CMT_PRIORITY_LEVEL18                   (0x00000002UL) /* Level 18 */
#define _CMT_PRIORITY_LEVEL19                   (0x00000003UL) /* Level 19 */
#define _CMT_PRIORITY_LEVEL20                   (0x00000004UL) /* Level 20 */
#define _CMT_PRIORITY_LEVEL21                   (0x00000005UL) /* Level 21 */
#define _CMT_PRIORITY_LEVEL22                   (0x00000006UL) /* Level 22 */
#define _CMT_PRIORITY_LEVEL23                   (0x00000007UL) /* Level 23 */
#define _CMT_PRIORITY_LEVEL24                   (0x00000008UL) /* Level 24 */
#define _CMT_PRIORITY_LEVEL25                   (0x00000009UL) /* Level 25 */
#define _CMT_PRIORITY_LEVEL26                   (0x0000000AUL) /* Level 26 */
#define _CMT_PRIORITY_LEVEL27                   (0x0000000BUL) /* Level 27 */
#define _CMT_PRIORITY_LEVEL28                   (0x0000000CUL) /* Level 28 */
#define _CMT_PRIORITY_LEVEL29                   (0x0000000DUL) /* Level 29 */
#define _CMT_PRIORITY_LEVEL30                   (0x0000000EUL) /* Level 30 */
#define _CMT_PRIORITY_LEVEL31                   (0x0000000FUL) /* Level 31 (lowest) */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Compare Match Timer Constant Register (CMCOR) */
#define _CMT4_CMCOR_VALUE                    (0x0008U)
/* Compare Match Timer Constant Register (CMCOR) */
#define _CMT5_CMCOR_VALUE                    (0x249EU)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_CMT4_Create(void);
void R_CMT4_Start(void);
void R_CMT4_Stop(void);
void R_CMT5_Create(void);
void R_CMT5_Start(void);
void R_CMT5_Stop(void);

/* Start user code for function. Do not edit comment generated here */

/* Counters used to generate user's delay period */
extern volatile uint32_t g_time_ms_count;
extern volatile uint32_t g_time_us_count;

/* End user code. Do not edit comment generated here */
#endif