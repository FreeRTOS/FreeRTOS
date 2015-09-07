/***********************************************************************************************************************
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
***********************************************************************************************************************/
/***********************************************************************************************************************
* System Name  : RZ/T1 Init program
* File Name    : r_reset.c
* Version      : 0.1
* Device       : R7S910018
* Abstract     : API for RESET and Low-Power function
* Tool-Chain   : GNUARM-NONEv14.02-EABI
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : RESET and Low-Power API of RZ/T1
* Limitation   : none
***********************************************************************************************************************/
/***********************************************************************************************************************
* History      : DD.MM.YYYY Version  Description
*              : 21.05.2015 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include <stdint.h>
#include "iodefine.h"
#include "r_system.h"
#include "r_reset.h"
#include "r_typedefs.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define RST_WRITE_ENABLE  (0x0000A502)
#define RST_WRITE_DISABLE (0x0000A500)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/



/***********************************************************************************************************************
Imported global variables and functions (from other files)
***********************************************************************************************************************/


/***********************************************************************************************************************
Exported global variables and functions (to be accessed by other files)
***********************************************************************************************************************/



/***********************************************************************************************************************
Private variables and functions
***********************************************************************************************************************/


/***********************************************************************************************************************
* Function Name : r_rst_write_enable
* Description   : Enables writing to the registers related to RESET and Low-
*                 Power function. And dummy read the register in order to fix 
*                 the register value.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void r_rst_write_enable(void)
{
    volatile uint32_t dummy; 

    UNUSED_VARIABLE(dummy);
  
    /* Enables writing to the Reset and Low-Power register */
    SYSTEM.PRCR.LONG = RST_WRITE_ENABLE;
    dummy = SYSTEM.PRCR.LONG;
    
}

/***********************************************************************************************************************
 End of function r_rst_write_enable
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name : r_rst_write_disable
* Description   : Disables writing to the registers related to RESET and Low-
*                 Power function. And dummy read the register in order to fix 
*                 the register value.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void r_rst_write_disable(void)
{
    volatile uint32_t dummy; 

    UNUSED_VARIABLE(dummy);
  
    /* Disables writing to the Reset and Low-Power register */
    SYSTEM.PRCR.LONG = RST_WRITE_DISABLE;
    dummy = SYSTEM.PRCR.LONG;
    
}

/***********************************************************************************************************************
 End of function r_rst_write_disable
***********************************************************************************************************************/

/* End of File */


