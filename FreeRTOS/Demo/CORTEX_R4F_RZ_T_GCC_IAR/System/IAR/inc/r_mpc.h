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
* File Name    : r_mpc.h
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for MPC function
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : MPC setting API of RZ/T1
* Limitation   : none
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/

#ifndef _R_MPC_HEADER_
#define _R_MPC_HEADER_

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/

/*******************************************************************************
Macro definitions
*******************************************************************************/
#define MPC_IRQ_DISABLE (0)
#define MPC_IRQ_ENABLE  (1)

#define MPC_PSEL_PT6_A21       (0x23)
#define MPC_PSEL_PT7_A22       (0x23)
#define MPC_PSEL_PK2_A23       (0x23)
#define MPC_PSEL_PK3_A24       (0x23)
#define MPC_PSEL_P97_A25       (0x23)
#define MPC_PSEL_P36_WE0_DQMLL (0x22)
#define MPC_PSEL_P37_WE1_DQMLU (0x22)
#define MPC_PSEL_PD1_CS1       (0x23)
#define MPC_PSEL_P45_CS2       (0x22)
#define MPC_PSEL_PT4_CS3       (0x23)
#define MPC_PSEL_P90_RAS       (0x23)
#define MPC_PSEL_PK0_CAS       (0x23)
#define MPC_PSEL_P24_RD_WR     (0x22)
#define MPC_PSEL_P46_CKE       (0x22)
#define MPC_PSEL_P10_CKIO      (0x22)
#define MPC_PSEL_P23_A0        (0x22) 
#define MPC_PSEL_PG0_A1        (0x22) 
#define MPC_PSEL_PG1_A2        (0x22) 
#define MPC_PSEL_PG2_A3        (0x22) 
#define MPC_PSEL_PG3_A4        (0x22) 
#define MPC_PSEL_PG4_A5        (0x22) 
#define MPC_PSEL_PG5_A6        (0x22) 
#define MPC_PSEL_PG6_A7        (0x22) 
#define MPC_PSEL_PG7_A8        (0x22) 
#define MPC_PSEL_PH0_A9        (0x22) 
#define MPC_PSEL_PH1_A10       (0x22)
#define MPC_PSEL_PH2_A11       (0x22)
#define MPC_PSEL_PH3_A12       (0x22)
#define MPC_PSEL_PH4_A13       (0x22)
#define MPC_PSEL_PH5_A14       (0x22)
#define MPC_PSEL_PH6_A15       (0x22)
#define MPC_PSEL_PH7_A16       (0x22)
#define MPC_PSEL_P20_A17       (0x22)
#define MPC_PSEL_P25_A18       (0x22)
#define MPC_PSEL_P26_A19       (0x22)
#define MPC_PSEL_P27_A20       (0x22)
#define MPC_PSEL_P00_D0        (0x22) 
#define MPC_PSEL_P01_D1        (0x22) 
#define MPC_PSEL_P02_D2        (0x22) 
#define MPC_PSEL_P03_D3        (0x22) 
#define MPC_PSEL_P04_D4        (0x22) 
#define MPC_PSEL_P05_D5        (0x22) 
#define MPC_PSEL_P06_D6        (0x22) 
#define MPC_PSEL_P07_D7        (0x22) 
#define MPC_PSEL_PE0_D8        (0x22) 
#define MPC_PSEL_PE1_D9        (0x22) 
#define MPC_PSEL_PE2_D10       (0x22)
#define MPC_PSEL_PE3_D11       (0x22)
#define MPC_PSEL_PE4_D12       (0x22)
#define MPC_PSEL_PE5_D13       (0x22)
#define MPC_PSEL_PE6_D14       (0x22)
#define MPC_PSEL_PE7_D15       (0x22)
#define MPC_PSEL_P22_RD        (0x22) 
#define MPC_PSEL_P21_CS0       (0x22)

/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/
void R_MPC_WriteEnable(void);
void R_MPC_WriteDisable(void);


#endif

/* End of File */
