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
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for CGC module.
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
#include "r_cg_cgc.h"
/* Start user code for include. Do not edit comment generated here */
#include "r_reset.h"
#include "r_system.h"
#include "r_typedefs.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */

#define CPG_WRITE_ENABLE        (0x0000A501)
#define CPG_WRITE_DISABLE       (0x0000A500)
  
#define CPG_CMT0_CLOCK_PCLKD_32 (1)
#define CPG_CMT0_CMI0_ENABLE    (1)
#define CPG_CMT0_CONST_100_US   (0xEA)
#define CPG_CMT0_START          (1)
#define CPG_CMT0_STOP           (0)

#define CPG_CMT_REG_CLEAR       (0x0000)

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_CGC_Create
* Description  : This function initializes the clock generator.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_CGC_Create(void)
{
    uint16_t w_count;

    /* LOCO circuit disable */
    SYSTEM.LOCOCR.BIT.LCSTP = 1U;

    /* Systen clock control register setting */
    SYSTEM.SCKCR.LONG = _CGC_CKIO_0 | _CGC_TCLK_0 | _CGC_PCLKE_0 | _CGC_PCLKF_0 | _CGC_PCLKG_0 | _CGC_SERICLK_0 | 
                        _CGC_ETCKE_0 | _CGC_ETCKD_0;

    /* Set the CPU frequency for PLL1 */
    SYSTEM.PLL1CR.BIT.CPUCKSEL = _CGC_PLL1_CPUCKSEL_600;

    /* PLL1 circuit enable */
    SYSTEM.PLL1CR2.BIT.PLL1EN = 1U;

    /* Wait 100us for PLL1 stabilization */
    for (w_count = 0U; w_count < _CGC_PLL_WAIT_CYCLE; w_count++)
    {
        nop();
    }

    /* Set system clock register 2 to PLL1 */
    SYSTEM.SCKCR2.BIT.CKSEL0 = 1U;

    /* Delta-sigma interface operation setting, DSCLK0 and DSCLK1 both in master mode */
    SYSTEM.DSCR.LONG = _CGC_DSSEL0_MASTER | _CGC_DSCLK0_0 | _CGC_DSSEL1_MASTER | _CGC_DSCLK1_0;
}

/* Start user code for adding. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name : R_CPG_WriteEnable
* Description   : Enables writing to the registers related to CPG function.
*                 And dummy read the register in order to fix the register value.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void R_CPG_WriteEnable(void)
{
    volatile uint32_t dummy = 0;

    UNUSED_VARIABLE(dummy);
  
    /* Enables writing to the CPG register */
    SYSTEM.PRCR.LONG = CPG_WRITE_ENABLE;
    dummy = SYSTEM.PRCR.LONG;
    
}

/***********************************************************************************************************************
 End of function R_CPG_WriteEnable
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name : R_CPG_WriteDisable
* Description   : Disables writing to the registers related to CPG function.
*                 And dummy read the register in order to fix the register value.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void R_CPG_WriteDisable(void)
{
    volatile uint32_t dummy = 0;

    UNUSED_VARIABLE(dummy);
  
    /* Disables writing to the CPG register */
    SYSTEM.PRCR.LONG = CPG_WRITE_DISABLE;
    dummy = SYSTEM.PRCR.LONG;
    
}

/***********************************************************************************************************************
 End of function R_CPG_WriteDisable
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name : R_CPG_PLLWait
* Description   : Wait about 100us for PLL stabilisation by using CMT0
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void R_CPG_PLLWait(void)
{
  
    /* Enables writing to the registers related to Reset and Low-Power function */
    r_rst_write_enable();
    
    /* Release from the CMT0 module-stop state  */
    MSTP(CMT0) = 0;
    
    /* Disables writing to the registers related to Reset and Low-Power function */
    r_rst_write_disable();
   
    /* Set CMT0 to 100us interval operation */
    CMT0.CMCR.BIT.CKS = CPG_CMT0_CLOCK_PCLKD_32;  
    CMT0.CMCR.BIT.CMIE = CPG_CMT0_CMI0_ENABLE;    
    CMT0.CMCNT = CPG_CMT_REG_CLEAR;              
    CMT0.CMCOR = CPG_CMT0_CONST_100_US;
    
    /* Set IRQ21(CMI0) for polling sequence */
    VIC.IEC0.BIT.IEC21 = 1U;
    VIC.PLS0.BIT.PLS21 = 1U;
    VIC.PIC0.BIT.PIC21 = 1U;
    
    /* Start CMT0 count */
    CMT.CMSTR0.BIT.STR0 = CPG_CMT0_START;

    /* Wait for 100us (IRQ21 is generated) */
    while ( !(VIC.RAIS0.BIT.RAI21) )
    {
        /* Wait */  
    }
        
    /* Stop CMT0 count */
    CMT.CMSTR0.BIT.STR0 = CPG_CMT0_STOP;
    
    /* Initialise CMT0 settings and clear interrupt detection edge */
    CMT0.CMCR.WORD = CPG_CMT_REG_CLEAR;
    CMT0.CMCNT = CPG_CMT_REG_CLEAR;
    CMT0.CMCOR = CPG_CMT_REG_CLEAR;
    CMT.CMSTR0.WORD = CPG_CMT_REG_CLEAR;
    
    VIC.PIC0.BIT.PIC21 = 1U;
    
    /* Enables writing to the registers related to Reset and Low-Power function */
    r_rst_write_enable();
    
    /* Set CMT0 to module-stop state */
    MSTP(CMT0) = 1;
    
    /* Disables writing to the registers related to Reset and Low-Power function */
    r_rst_write_disable();
}

/***********************************************************************************************************************
 End of function R_CPG_PLLWait
***********************************************************************************************************************/

/* End user code. Do not edit comment generated here */
