/* Adapted for use with IAR Embedded Workbench */
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
* Copyright (C) 2013, 2014 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_intprg.c
* Version      : Code Generator for RX64M V1.00.01.01 [09 May 2014]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : IAR Embedded Workbench
* Description  : Setting of B.
* Creation Date: 30/06/2014
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
#include <machine.h>
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/


// fixedint.c in $TOOLKIT$/rx/src/lib/src
/* Undefined exceptions for supervisor instruction, undefined instruction and floating point exceptions */
__interrupt void __undefined_handler (void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* NMI */
__interrupt void __NMI_handler (void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}


/* BRK */
#pragma vector=0
__interrupt void r_brk_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* ICU GROUPBE0 */
#pragma vector=VECT(ICU,GROUPBE0)
__interrupt void r_icu_group_be0_interrupt(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}


/* ICU GROUPBL0 */
#pragma vector=VECT(ICU,GROUPBL0)
__interrupt void r_icu_group_bl0_interrupt(void)
{
    if (ICU.GRPBL0.BIT.IS14 == 1U)
    {
        r_sci7_transmitend_interrupt();
    }
    if (ICU.GRPBL0.BIT.IS15 == 1U)
    {
        r_sci7_receiveerror_interrupt();
    }
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* ICU GROUPBL1 */
#pragma vector=VECT(ICU,GROUPBL1)
__interrupt void r_icu_group_bl1_interrupt(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* ICU GROUPAL0 */
#pragma vector=VECT(ICU,GROUPAL0)
__interrupt void r_icu_group_al0_interrupt(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* ICU GROUPAL1 */
#pragma vector=VECT(ICU,GROUPAL1)
__interrupt void r_icu_group_al1_interrupt(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
