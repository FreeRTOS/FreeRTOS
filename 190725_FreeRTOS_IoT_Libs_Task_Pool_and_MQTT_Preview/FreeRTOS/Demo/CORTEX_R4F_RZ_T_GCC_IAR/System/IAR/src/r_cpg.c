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
* File Name    : r_cpg.c
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for CPG function
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : CPG setting API of RZ/T1
* Limitation   : none
*******************************************************************************/
/*******************************************************************************
* History      : DD.MM.YYYY Version  Description
*              :                     First Release
*******************************************************************************/

/*******************************************************************************
Includes <System Includes> , "Project Includes"
*******************************************************************************/
#include <stdint.h>
#include <Renesas/ior7s910017.h>
#include "r_system.h"
#include "r_cpg.h"
#include "r_reset.h"
#include "r_icu_init.h"

/*******************************************************************************
Macro definitions
*******************************************************************************/
#define CPG_WRITE_ENABLE (0x0000A501)
#define CPG_WRITE_DISABLE (0x0000A500)

#define CPG_CMT0_CLOCK_PCLKD_32 (1)
#define CPG_CMT0_CMI0_ENABLE    (1)
#define CPG_CMT0_CONST_100_us   (0xEA)
#define CPG_CMT0_START          (1)
#define CPG_CMT0_STOP           (0)

#define CPG_CMT_REG_CLEAR (0x0000)

/*******************************************************************************
Typedef definitions
*******************************************************************************/


/*******************************************************************************
Imported global variables and functions (from other files)
*******************************************************************************/


/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/


/*******************************************************************************
Private variables and functions
*******************************************************************************/


/*******************************************************************************
* Function Name : R_CPG_PLL_Wait
* Description   : Wait about 100us for PLL stabilization by using CMT0
* Arguments    : none
* Return Value : none
*******************************************************************************/
void R_CPG_PLL_Wait(void)
{

    /* Enables writing to the registers related to Reset and Low-Power function */
    r_rst_write_enable();

    /* Release from the CMT0 module-stop state  */
    MSTP(CMT0) = 0;

    /* Disables writing to the registers related to Reset and Low-Power function */
    r_rst_write_disable();

    /* Set CMT0 to 100us interval operation */
    CMT0.CMCR.BIT.CKS = CPG_CMT0_CLOCK_PCLKD_32;  // Count clock = PCLKD/32
    CMT0.CMCR.BIT.CMIE = CPG_CMT0_CMI0_ENABLE;    // Enable CMI0 interrupt
    CMT0.CMCNT = CPG_CMT_REG_CLEAR;              // Clear CMCNT counter
    CMT0.CMCOR = CPG_CMT0_CONST_100_us;           // Set constant value for 100us


    /* Set IRQ21(CMI0) for polloing sequence */
    VIC.IEC0.BIT.IEC21 = ICU_IEC_MASK_SET;    // Mask IRQ21 interrupt
    VIC.PLS0.BIT.PLS21 = ICU_TYPE_EDGE;       // Set EDGE type interrupt
    VIC.PIC0.BIT.PIC21 = ICU_PIC_EDGE_CLEAR;  // Clear interrupt detection edge

    /* Enable IRQ interrupt (Clear CPSR.I bit to 0) */
    asm("cpsie i");   // Clear CPSR.I bit to 0
    asm("isb");       // Ensuring Context-changing

    /* Start CMT0 count */
    CMT.CMSTR0.BIT.STR0 = CPG_CMT0_START;

    /* Wait for 100us (IRQ21 is generated) */
    while ( !(VIC.RAIS0.BIT.RAI21) )
    {
        /* Wait */
    }

    /* Stop CMT0 count */
    CMT.CMSTR0.BIT.STR0 = CPG_CMT0_STOP;

    /* Initialize CMT0 settings and clear interrupt detection edge */
    CMT0.CMCR.WORD = CPG_CMT_REG_CLEAR;
    CMT0.CMCNT = CPG_CMT_REG_CLEAR;
    CMT0.CMCOR = CPG_CMT_REG_CLEAR;
    CMT.CMSTR0.WORD = CPG_CMT_REG_CLEAR;

    VIC.PIC0.BIT.PIC21 = ICU_PIC_EDGE_CLEAR;  // Clear interrupt detection edge


    /* Disable IRQ interrupt (Set CPSR.I bit to 1) */
    asm("cpsid i");
    asm("isb");

    /* Enables writing to the registers related to Reset and Low-Power function */
    r_rst_write_enable();

    /* Set CMT0 to module-stop state */
    MSTP(CMT0) = 1;

    /* Disables writing to the registers related to Reset and Low-Power function */
    r_rst_write_disable();


}

/*******************************************************************************
 End of function R_CPG_PLL_Wait
*******************************************************************************/

/* End of File */


