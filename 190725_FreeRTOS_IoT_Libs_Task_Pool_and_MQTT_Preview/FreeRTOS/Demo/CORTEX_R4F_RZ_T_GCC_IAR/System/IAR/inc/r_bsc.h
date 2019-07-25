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
* Description  : BSC setting API of RZ/T1
* Limitation   : none
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/

#ifndef _R_BSC_HEADER_
#define _R_BSC_HEADER_

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/

/*******************************************************************************
Macro definitions
*******************************************************************************/
#define BSC_IDLE_CYCLE_0  (0)
#define BSC_IDLE_CYCLE_1  (1)
#define BSC_IDLE_CYCLE_2  (2)
#define BSC_IDLE_CYCLE_4  (3)
#define BSC_IDLE_CYCLE_6  (4)
#define BSC_IDLE_CYCLE_8  (5)
#define BSC_IDLE_CYCLE_10 (6)
#define BSC_IDLE_CYCLE_12 (7)

#define BSC_TYPE_NORMAL          (0)
#define BSC_TYPE_BURST_ROM_ASYNC (1)
#define BSC_TYPE_MPX_IO          (2)
#define BSC_TYPE_SRAM_BYTE       (3)
#define BSC_TYPE_SDRAM           (4)
#define BSC_TYPE_BURST_ROM_SYNC  (7)

#define BSC_WIDTH_8_BIT  (1)
#define BSC_WIDTH_16_BIT (2)
#define BSC_WIDTH_32_BIT (3)

#define BSC_DELAY_STATE_CYCLE_0_5 (0)
#define BSC_DELAY_STATE_CYCLE_1_5 (1)
#define BSC_DELAY_STATE_CYCLE_2_5 (2)
#define BSC_DELAY_STATE_CYCLE_3_5 (3)

#define BSC_EXT_WAIT_VALID   (0)
#define BSC_EXT_WAIT_IGNORED (1)

#define BSC_ACCESS_WAIT_0  (0)
#define BSC_ACCESS_WAIT_1  (1)
#define BSC_ACCESS_WAIT_2  (2)
#define BSC_ACCESS_WAIT_3  (3)
#define BSC_ACCESS_WAIT_4  (4)
#define BSC_ACCESS_WAIT_5  (5)
#define BSC_ACCESS_WAIT_6  (6)
#define BSC_ACCESS_WAIT_8  (7)
#define BSC_ACCESS_WAIT_10 (8)
#define BSC_ACCESS_WAIT_12 (9)
#define BSC_ACCESS_WAIT_14 (10)
#define BSC_ACCESS_WAIT_18 (11)
#define BSC_ACCESS_WAIT_24 (12)

#define BSC_WRITE_ACCESS_WAIT_SAME (0)  // Set same settings of WR[3:0]bit
#define BSC_WRITE_ACCESS_WAIT_0    (1)
#define BSC_WRITE_ACCESS_WAIT_1    (2)
#define BSC_WRITE_ACCESS_WAIT_2    (3)
#define BSC_WRITE_ACCESS_WAIT_3    (4)
#define BSC_WRITE_ACCESS_WAIT_4    (5)
#define BSC_WRITE_ACCESS_WAIT_5    (6)
#define BSC_WRITE_ACCESS_WAIT_6    (7)

#define BSC_BYTE_ENABLE_RD_WR (0)
#define BSC_BYTE_ENABLE_WE    (1)

#define BSC_CAS_LATENCY_1 (0)
#define BSC_CAS_LATENCY_2 (1)
#define BSC_CAS_LATENCY_3 (2)
#define BSC_CAS_LATENCY_4 (3)

#define BSC_WTRC_IDLE_2 (0)
#define BSC_WTRC_IDLE_3 (1)
#define BSC_WTRC_IDLE_5 (2)
#define BSC_WTRC_IDLE_8 (3)

#define BSC_TRWL_CYCLE_0 (0)
#define BSC_TRWL_CYCLE_1 (1)
#define BSC_TRWL_CYCLE_2 (2)
#define BSC_TRWL_CYCLE_3 (3)

#define BSC_PRECHARGE_0 (0x00000000)
#define BSC_PRECHARGE_1 (0x00000008)
#define BSC_PRECHARGE_2 (0x00000010)
#define BSC_PRECHARGE_3 (0x00000018)

#define BSC_WTRCD_WAIT_0 (0) 
#define BSC_WTRCD_WAIT_1 (1)
#define BSC_WTRCD_WAIT_2 (2)
#define BSC_WTRCD_WAIT_3 (3)

#define BSC_WTRP_WAIT_0 (0) 
#define BSC_WTRP_WAIT_1 (1)
#define BSC_WTRP_WAIT_2 (2)
#define BSC_WTRP_WAIT_3 (3)

#define BSC_ROW_11_BIT (0)
#define BSC_ROW_12_BIT (1)
#define BSC_ROW_13_BIT (2)

#define BSC_COL_8_BIT  (0)
#define BSC_COL_9_BIT  (1)
#define BSC_COL_10_BIT (2)

#define BSC_BACTV_AUTO (0)
#define BSC_BACTV_BANK (1)

#define BSC_PDOWN_INVALID (0)
#define BSC_PDOWN_VALID   (1)

#define BSC_RMODE_AUTO (0)
#define BSC_RMODE_SELF (1)

#define BSC_RFSH_NONE (0)
#define BSC_RFSH_DONE (1)

#define BSC_DEEP_SELF (0)
#define BSC_DEEP_DEEP (1)

#define BSC_PROTECT_KEY (0xA55A0000)

#define BSC_RFSH_TIME_1 (0)
#define BSC_RFSH_TIME_2 (1)
#define BSC_RFSH_TIME_4 (2)
#define BSC_RFSH_TIME_6 (3)
#define BSC_RFSH_TIME_8 (4)

#define BSC_CKS_DIV_STOP (0x00000000)
#define BSC_CKS_DIV_4    (0x00000008)
#define BSC_CKS_DIV_16   (0x00000010)
#define BSC_CKS_DIV_64   (0x00000018)
#define BSC_CKS_DIV_256  (0x00000020)
#define BSC_CKS_DIV_1024 (0x00000028)
#define BSC_CKS_DIV_2048 (0x00000030)
#define BSC_CKS_DIV_4096 (0x00000038)

#define BSC_CMIE_DISABLE (0x00000000)
#define BSC_CMIE_ENABLE  (0x00000040)

/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/



#endif

/* End of File */
