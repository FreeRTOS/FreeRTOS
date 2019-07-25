/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only 
* intended for use with Renesas products. No other uses are authorized. This 
* software is owned by Renesas Electronics Corporation and is protected under 
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING 
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT 
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE 
* AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR 
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE 
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software 
* and to discontinue the availability of this software.  By using this software, 
* you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_cmt.h
* Version      : Applilet4 for RX64M V1.00.00.00 [02 Aug 2013]
* Device(s)    : R5F564MLHxFC
* Tool-Chain   : CCRX
* Description  : This file implements device driver for CMT module.
* Creation Date: 07/02/2014
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
#define _0000_CMT_CMCR_CKS_PCLK8                (0x0000U) /* PCLK/8 */
#define _0001_CMT_CMCR_CKS_PCLK32               (0x0001U) /* PCLK/32 */
#define _0002_CMT_CMCR_CKS_PCLK128              (0x0002U) /* PCLK/128 */
#define _0003_CMT_CMCR_CKS_PCLK512              (0x0003U) /* PCLK/512 */
/* Compare Match Interrupt Enable (CMIE) */
#define _0000_CMT_CMCR_CMIE_DISABLE             (0x0000U) /* Compare match interrupt (CMIn) disabled */
#define _0040_CMT_CMCR_CMIE_ENABLE              (0x0040U) /* Compare match interrupt (CMIn) enabled */

/*
    Interrupt Source Priority Register n (IPRn)
*/
/* Interrupt Priority Level Select (IPR[3:0]) */
#define _00_CMT_PRIORITY_LEVEL0                 (0x00U) /* Level 0 (interrupt disabled) */
#define _01_CMT_PRIORITY_LEVEL1                 (0x01U) /* Level 1 */
#define _02_CMT_PRIORITY_LEVEL2                 (0x02U) /* Level 2 */
#define _03_CMT_PRIORITY_LEVEL3                 (0x03U) /* Level 3 */
#define _04_CMT_PRIORITY_LEVEL4                 (0x04U) /* Level 4 */
#define _05_CMT_PRIORITY_LEVEL5                 (0x05U) /* Level 5 */
#define _06_CMT_PRIORITY_LEVEL6                 (0x06U) /* Level 6 */
#define _07_CMT_PRIORITY_LEVEL7                 (0x07U) /* Level 7 */
#define _08_CMT_PRIORITY_LEVEL8                 (0x08U) /* Level 8 */
#define _09_CMT_PRIORITY_LEVEL9                 (0x09U) /* Level 9 */
#define _0A_CMT_PRIORITY_LEVEL10                (0x0AU) /* Level 10 */
#define _0B_CMT_PRIORITY_LEVEL11                (0x0BU) /* Level 11 */
#define _0C_CMT_PRIORITY_LEVEL12                (0x0CU) /* Level 12 */
#define _0D_CMT_PRIORITY_LEVEL13                (0x0DU) /* Level 13 */
#define _0E_CMT_PRIORITY_LEVEL14                (0x0EU) /* Level 14 */
#define _0F_CMT_PRIORITY_LEVEL15                (0x0FU) /* Level 15 (highest) */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Compare Match Timer Constant Register (CMCOR) */
#define _B71B_CMT0_CMCOR_VALUE                  (0xB71BU)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_CMT0_Create(void);
void R_CMT0_Start(void);
void R_CMT0_Stop(void);

/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif