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
* File Name    : r_cg_mpc.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : Setting of port and mpc registers.
* Creation Date: 22/04/2015
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */
#include "r_typedefs.h"
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_mpc.h"
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name: R_MPC_Create
* Description  : This function initializes the Port I/O.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_MPC_Create(void)
{
    /* Set RSPCK1 pin */
    MPC.PN3PFS.BYTE |= 0x0EU;
    PORTN.PMR.BYTE |= 0x08U;
    /* Set MOSI1 pin */
    MPC.PN2PFS.BYTE |= 0x0EU;
    PORTN.PMR.BYTE |= 0x04U;
    /* Set MISO1 pin */
    MPC.PN1PFS.BYTE |= 0x0EU;
    PORTN.PMR.BYTE |= 0x02U;
    /* Set SSL10 pin */
    MPC.PN0PFS.BYTE |= 0x0EU;
    PORTN.PMR.BYTE |= 0x01U;
    /* Set SSL11 pin */
    MPC.PN4PFS.BYTE |= 0x0EU;
    PORTN.PMR.BYTE |= 0x10U;
    /* Set TXD2 pin */
    MPC.P91PFS.BYTE |= 0x0BU;
    PORT9.PMR.BYTE |= 0x02U;
    /* Set RXD2 pin */
    MPC.P92PFS.BYTE |= 0x0BU;
    PORT9.PMR.BYTE |= 0x04U;
    /* Set IRQ12 pin */
    MPC.P44PFS.BYTE |= 0x40U;
    PORT4.PMR.BYTE &= 0xEFU;
    PORT4.PDR.WORD &= 0xFEFFU;
    PORT4.PDR.WORD |= 0x0200U;
    /* Set TIOCB9 pin */
    MPC.PL0PFS.BYTE |= 0x03U;
    PORTL.PMR.BYTE |= 0x01U;
    /* Set TIOCC9 pin */
    MPC.PU4PFS.BYTE |= 0x03U;
    PORTU.PMR.BYTE |= 0x10U;
    /* Set TIOCD9 pin */
    MPC.PN5PFS.BYTE |= 0x03U;
    PORTN.PMR.BYTE |= 0x20U;

    R_MPC_Create_UserInit();
}
/***********************************************************************************************************************
* Function Name: R_MPC_Create_UserInit
* Description  : This function adds user code after initializing modules pin setting.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_MPC_Create_UserInit(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/* Start user code for adding. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name : R_MPC_WriteEnable
* Description   : Enables writing to the PmnPFS register (m = 0-9, A-U, n = 0-7).
                  And dummy read the register in order to fix the register value.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void R_MPC_WriteEnable(void)
{
    volatile uint8_t dummy=0;

    UNUSED_VARIABLE(dummy);
  
    /* Enables writing to the PmnPFS register */
    MPC.PWPR.BYTE = MPC_PFSWE_WRITE_ENABLE;  
    dummy = MPC.PWPR.BYTE;
    MPC.PWPR.BYTE = MPC_PFS_WRITE_ENABLE; 
    dummy = MPC.PWPR.BYTE;
    
}

/***********************************************************************************************************************
 End of function R_MPC_WriteEnable
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name : R_MPC_WriteDisable
* Description   : Disables writing to the PmnPFS register (m = 0-9, A-U, n = 0-7).
                  And dummy read the register in order to fix the register value.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void R_MPC_WriteDisable(void)
{
    volatile uint8_t dummy=0;

    UNUSED_PARAM(dummy);
  
    /* Disables writing to the PmnPFS register */
    MPC.PWPR.BYTE = MPC_PFS_WRITE_DISABLE;  
    dummy = MPC.PWPR.BYTE;
    
}

/***********************************************************************************************************************
 End of function R_MPC_WriteDisable
***********************************************************************************************************************/

/* End user code. Do not edit comment generated here */
