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
* File Name    : r_cg_icu.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for ICU module.
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
#include "r_cg_icu.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_ICU_Create
* Description  : This function initializes ICU module.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_ICU_Create(void)
{

    /* Disable IRQ12 interrupt */
    VIC.IEC0.LONG = 0x00010000UL;

    /* Set IRQ12 edge detection type */
    VIC.PLS0.LONG |= 0x00010000UL;
    ICU.IRQCR12.BIT.IRQMD = (uint8_t)_ICU_IRQ_EDGE_FALLING;

    /* Enable IRQ12 digital filter */
    ICU.IRQFLTE.BIT.FLTEN12 = 1U;

    /* Set IRQ12 digital filter clock */
    ICU.IRQFLTC.BIT.FCLKSEL12 = _ICU_IRQ12_FILTER_PCLKB_64;

    /* Set IRQ12 Priority */
    VIC.PRL16.LONG = _ICU_PRIORITY_LEVEL3;

    /* Set IRQ12 interupt address */
    VIC.VAD16.LONG = (uint32_t)r_icu_irq12_interrupt;
}
/***********************************************************************************************************************
* Function Name: R_ICU_IRQ12_Start
* Description  : This function enables IRQ12 interrupt.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_ICU_IRQ12_Start(void)
{
    /* Enable IRQ12 interrupt */
    VIC.IEN0.LONG |= 0x00010000UL;
}
/***********************************************************************************************************************
* Function Name: R_ICU_IRQ12_Stop
* Description  : This function disables IRQ12 interrupt.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_ICU_IRQ12_Stop(void)
{
    /* Disable IRQ12 interrupt */
    VIC.IEC0.LONG = 0x00010000UL;
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
