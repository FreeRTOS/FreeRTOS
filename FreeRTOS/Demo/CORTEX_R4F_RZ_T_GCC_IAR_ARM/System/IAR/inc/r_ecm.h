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
* File Name    : r_ecm.h
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for ecm function
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : ecm function API of RZ/T1
* Limitation   : none
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/

#ifndef _R_ECM_HEADER_
#define _R_ECM_HEADER_


/*******************************************************************************
Macro definitions
*******************************************************************************/
#define ECM_COMMAND_KEY (0x000000A5)


/*******************************************************************************
Typedef definitions
*******************************************************************************/
typedef enum
{
    ECM_MASTER,
    ECM_CHECKER,
    ECM_COMMON,
    ECM_TYPE_MAX
} ecm_reg_type_t;

/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/
void R_ECM_Init(void);
void R_ECM_CompareError_Wait(void);
uint8_t R_ECM_Write_Reg8(uint8_t reg_type, volatile unsigned char *reg, uint8_t value);
uint8_t R_ECM_Write_Reg32(uint8_t reg_type, volatile unsigned long *reg, uint32_t value);

#endif

/* End of File */
