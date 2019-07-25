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
* File Name    : r_ram_init.c
* Version      : 0.1
* Device       : R7S9100xx
* Abstract     : API for internal extended RAM function
* Tool-Chain   : IAR Embedded Workbench Ver.7.20
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : internal extended RAM setting API of RZ/T1
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
#include "r_ram_init.h"

/*******************************************************************************
Macro definitions
*******************************************************************************/
#define RAM_ECC_ENABLE (0x00000001)
#define RAM_ECC_DISABLE (0x00000000)
#define RAM_PROTECT (0x00000000)

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
* Function Name : R_RAM_ECC_Enable
* Description   : Enable ECC function for internal extended RAM.
* Arguments    : none
* Return Value : none
*******************************************************************************/
void R_RAM_ECC_Enable(void)
{
    /* Enables writing to the protected registers related to RAM function */
    R_RAM_WriteEnable();
  
    /* Enable ECC function */
    ECCRAM.RAMEDC.LONG = RAM_ECC_ENABLE;
    
    /* Disables writing to the protected registers related to RAM function */
    R_RAM_WriteDisable();
    
}

/*******************************************************************************
 End of function R_RAM_ECC_Enable
*******************************************************************************/


/*******************************************************************************
* Function Name : R_RAM_WriteEnable
* Description   : Enable writing to the protected registers related to RAM.
*                 And dummy read the register in order to fix the register value.
* Arguments    : none
* Return Value : none
*******************************************************************************/
void R_RAM_WriteEnable(void)
{
    volatile uint32_t dummy; 
    
    /* Special sequence for protect release */
    ECCRAM.RAMPCMD.LONG = 0x000000A5;  // Write fixed value 0x000000A5
    ECCRAM.RAMPCMD.LONG = 0x00000001;  // Write expected value 
    ECCRAM.RAMPCMD.LONG = 0x0000FFFE;  // Write inversed value of the expected value
    ECCRAM.RAMPCMD.LONG = 0x00000001;  // Write expected value again
    dummy = ECCRAM.RAMPCMD.LONG;        
    
}

/*******************************************************************************
 End of function R_RAM_WriteEnable
*******************************************************************************/

/*******************************************************************************
* Function Name : R_RAM_WriteDisable
* Description   : Disable writing to the protected registers related to RAM.
*                 And dummy read the register in order to fix the register value.
* Arguments    : none
* Return Value : none
*******************************************************************************/
void R_RAM_WriteDisable(void)
{
    volatile uint32_t dummy; 
    
    /* Clear RAMPCMD register to zero */
    ECCRAM.RAMPCMD.LONG = RAM_PROTECT;   
    dummy = ECCRAM.RAMPCMD.LONG; 
    
}

/*******************************************************************************
 End of function R_RAM_WriteDisable
*******************************************************************************/

/* End of File */


