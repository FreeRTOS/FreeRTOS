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
* File Name    : r_cg_intprg.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : Set the non-maskable interrupt.
* Creation Date: 22/04/2015
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/***********************************************************************************************************************
* Function Name: r_set_exception_handler
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_set_exception_handler(void)
{
    uint32_t *pointer;

    /* FIQ exception handler address */
    pointer = (uint32_t *)0x1c;

    /* Branch to next address instruction */
    *pointer ++ = 0xeaffffff;

    /* LDR PC,[PC, #-0x04], load r_fiq_handler address to PC */
    *pointer ++ = 0xe51ff004;

    /* DC32 r_fiq_handler, define the r_fiq_handler address */
    *pointer = (uint32_t)r_fiq_handler;

    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_fiq_handler
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#ifdef __ICCARM__
	__irq __arm
#endif /* __ICCARM__ */
void r_fiq_handler(void)
{
    while(1);
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}


/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
