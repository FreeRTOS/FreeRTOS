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
* File Name    : r_cg_cmt.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for CMT module.
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
#include "r_cg_cmt.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_CMT4_Create
* Description  : This function initializes the CMT4 channel.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CMT4_Create(void)
{
    /* Disable CMI4 interrupt */
    VIC.IEC9.LONG = 0x00000800UL;

    /* Cancel CMT stop state in LPC */
    MSTP(CMT2) = 0U;

    /* Set control registers */
    CMT4.CMCR.WORD = _CMT_CMCR_CKS_PCLK8 | _CMT_CMCR_CMIE_ENABLE;
    CMT4.CMCOR = _CMT4_CMCOR_VALUE;

    /* Set CMI4 edge detection type */
    VIC.PLS9.LONG |= 0x00000800UL;

    /* Set CMI4 priority level */
    VIC.PRL299.LONG = _CMT_PRIORITY_LEVEL16;

    /* Set CMI4 interrupt address */
    VIC.VAD299.LONG = (uint32_t)r_cmt_cmi4_interrupt;
}
/***********************************************************************************************************************
* Function Name: R_CMT4_Start
* Description  : This function starts the CMT4 channel counter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CMT4_Start(void)
{
    /* Enable CMI4 interrupt in ICU */
    VIC.IEN9.LONG |= 0x00000800UL;

    /* Start CMT4 count */
    CMT.CMSTR2.BIT.STR4 = 1U;
}
/***********************************************************************************************************************
* Function Name: R_CMT4_Stop
* Description  : This function stops the CMT4 channel counter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CMT4_Stop(void)
{
    /* Disable CMI4 interrupt in ICU */
    VIC.IEC9.LONG = 0x00000800UL;

    /* Stop CMT4 count */
    CMT.CMSTR2.BIT.STR4 = 0U;
}
/***********************************************************************************************************************
* Function Name: R_CMT5_Create
* Description  : This function initializes the CMT5 channel.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CMT5_Create(void)
{
    /* Disable CMI5 interrupt */
    VIC.IEC9.LONG = 0x00001000UL;

    /* Cancel CMT stop state in LPC */
    MSTP(CMT2) = 0U;

    /* Set control registers */
    CMT5.CMCR.WORD = _CMT_CMCR_CKS_PCLK8 | _CMT_CMCR_CMIE_ENABLE;
    CMT5.CMCOR = _CMT5_CMCOR_VALUE;

    /* Set CMI5 edge detection type */
    VIC.PLS9.LONG |= 0x00001000UL;

    /* Set CMI5 priority level */
    VIC.PRL300.LONG = _CMT_PRIORITY_LEVEL17;

    /* Set CMI5 interrupt address */
    VIC.VAD300.LONG = (uint32_t)r_cmt_cmi5_interrupt;
}
/***********************************************************************************************************************
* Function Name: R_CMT5_Start
* Description  : This function starts the CMT5 channel counter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CMT5_Start(void)
{
    /* Enable CMI5 interrupt in ICU */
    VIC.IEN9.LONG |= 0x00001000UL;

    /* Start CMT5 count */
    CMT.CMSTR2.BIT.STR5 = 1U;
}
/***********************************************************************************************************************
* Function Name: R_CMT5_Stop
* Description  : This function stops the CMT5 channel counter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CMT5_Stop(void)
{
    /* Disable CMI5 interrupt in ICU */
    VIC.IEC9.LONG = 0x00001000UL;

    /* Stop CMT5 count */
    CMT.CMSTR2.BIT.STR5 = 0U;
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
