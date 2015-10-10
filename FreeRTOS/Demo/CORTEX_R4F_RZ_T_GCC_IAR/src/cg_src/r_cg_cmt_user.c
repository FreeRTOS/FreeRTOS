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
* File Name    : r_cg_cmt_user.c
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

/* Counters used to generate user's delay period */
volatile uint32_t g_time_ms_count;
volatile uint32_t g_time_us_count;

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: r_cmt_cmi4_interrupt
* Description  : This function is CMI4 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#ifdef __ICCARM__
	__arm __irq
#endif
void r_cmt_cmi4_interrupt(void)
{
    /* Clear the interrupt source CMI4 */
    VIC.PIC9.LONG = 0x00000800UL;

    /* Start user code. Do not edit comment generated here */

    /* Decrement the count value */
    g_time_us_count--;

    /* End user code. Do not edit comment generated here */

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_cmt_cmi5_interrupt
* Description  : This function is CMI5 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#ifdef __ICCARM__
	__arm __irq
#endif
void r_cmt_cmi5_interrupt(void)
{
    /* Clear the interrupt source CMI5 */
    VIC.PIC9.LONG = 0x00001000UL;

    /* Start user code. Do not edit comment generated here */

    /* Decrement the count value */
    g_time_ms_count--;

    /* End user code. Do not edit comment generated here */

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
