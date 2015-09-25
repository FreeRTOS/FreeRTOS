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
* File Name    : r_cg_cgc.c
* Version      : Code Generator for RX113 V1.02.01.02 [28 May 2015]
* Device(s)    : R5F51138AxFP
* Tool-Chain   : CCRX
* Description  : This file implements device driver for CGC module.
* Creation Date: 21/09/2015
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
#include "r_cg_cgc.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_CGC_Create
* Description  : This function initializes the clock generator.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CGC_Create(void)
{
    uint32_t sckcr_dummy;
    uint32_t w_count;

    /* Set main clock control registers */
    SYSTEM.MOFCR.BYTE = _00_CGC_MAINOSC_RESONATOR | _20_CGC_MAINOSC_OVER10M;
    SYSTEM.MOSCWTCR.BYTE = _06_CGC_OSC_WAIT_CYCLE_32768;

    /* Set main clock operation */
    SYSTEM.MOSCCR.BIT.MOSTP = 0U;

    /* Wait for main clock oscillator wait counter overflow */
    while (1U != SYSTEM.OSCOVFSR.BIT.MOOVF);

    /* Set system clock */
    sckcr_dummy = _00000000_CGC_PCLKD_DIV_1 | _00000000_CGC_PCLKB_DIV_1 | _00000000_CGC_ICLK_DIV_1 | 
                  _00000000_CGC_FCLK_DIV_1;
    SYSTEM.SCKCR.LONG = sckcr_dummy;

    while (SYSTEM.SCKCR.LONG != sckcr_dummy);

    /* Set PLL circuit */
    SYSTEM.PLLCR.WORD = _0002_CGC_PLL_FREQ_DIV_4 | _0F00_CGC_PLL_FREQ_MUL_8;
    SYSTEM.PLLCR2.BIT.PLLEN = 0U;

    /* Wait for PLL wait counter overflow */
    while (1U != SYSTEM.OSCOVFSR.BIT.PLOVF);

    /* Stop sub-clock */
    SYSTEM.SOSCCR.BIT.SOSTP = 1U;

    /* Wait for the register modification to complete */
    while (1U != SYSTEM.SOSCCR.BIT.SOSTP);

    /* Stop sub-clock */
    RTC.RCR3.BIT.RTCEN = 0U;

    /* Wait for the register modification to complete */
    while (0U != RTC.RCR3.BIT.RTCEN);

    /* Wait for 5 sub-clock cycles */
    for (w_count = 0U; w_count < _007B_CGC_SUBSTPWT_WAIT; w_count++)
    {
        __asm volatile( "NOP" );
    }

    /* Set sub-clock drive capacity */
    RTC.RCR3.BIT.RTCDV = 1U;

    /* Wait for the register modification to complete */
    while (1U != RTC.RCR3.BIT.RTCDV);

    /* Set sub-clock */
    SYSTEM.SOSCCR.BIT.SOSTP = 0U;

    /* Wait for the register modification to complete */
    while (0U != SYSTEM.SOSCCR.BIT.SOSTP);

    /* Wait for sub-clock to be stable */
    for (w_count = 0U; w_count < _00061A81_CGC_SUBOSCWT_WAIT; w_count++)
    {
        __asm volatile( "NOP" );
    }

    /* Set clock source */
    SYSTEM.SCKCR3.WORD = _0400_CGC_CLOCKSOURCE_PLL;

    while (SYSTEM.SCKCR3.WORD != _0400_CGC_CLOCKSOURCE_PLL);

    /* Set LOCO */
    SYSTEM.LOCOCR.BIT.LCSTP = 1U;
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
