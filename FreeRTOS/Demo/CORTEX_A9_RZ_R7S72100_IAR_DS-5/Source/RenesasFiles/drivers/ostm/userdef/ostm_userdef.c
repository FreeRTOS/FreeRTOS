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
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name    : ostm_userdef.c
* $Rev: $
* $Date::                           $
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.13
*              : ARM Complier
* OS           : 
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - OS timer device driver (User define function)
* Operation    : 
* Limitations  : 
*******************************************************************************/

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "dev_drv.h"                /* Device Driver common header */
#include "devdrv_ostm.h"            /* OSTM Driver header */
#include "devdrv_intc.h"            /* INTC Driver Header */
#include "iodefine.h"
#include "main.h"

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/
#define P0_CLOCK_FREQUENCY_kHz  (33.333 * 1000)     /* 33.333MHz */
#define MAX_CYCLE_msec          (0xFFFFFFFF / P0_CLOCK_FREQUENCY_kHz)

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/

/******************************************************************************
Private global variables and functions
******************************************************************************/
static volatile uint8_t ostm_int_flg;

/******************************************************************************
* Function Name: Userdef_OSTM0_Init
* Description  :
* Arguments    : uint32_t mode
*              : uint32_t cycle
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t Userdef_OSTM0_Init(uint32_t mode, uint32_t cycle)
{
    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: Userdef_OSTM1_Init
* Description  :
* Arguments    : uint32_t mode
*              : uint32_t cycle
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t Userdef_OSTM1_Init(uint32_t mode, uint32_t cycle)
{
    return 0;
}

/******************************************************************************
* Function Name: Userdef_OSTM0_Int
* Description  : 
* Arguments    : 
* Return Value : none
******************************************************************************/
void Userdef_OSTM0_Int(void)
{
}

/******************************************************************************
* Function Name: Userdef_OSTM1_Int
* Description  : 
* Arguments    : 
* Return Value : none
******************************************************************************/
void Userdef_OSTM1_Int(void)
{
}

/******************************************************************************
* Function Name: Userdef_OSTM0_WaitInt
* Description  : 
* Arguments    : 
* Return Value : none
******************************************************************************/
void Userdef_OSTM0_WaitInt(void)
{
}

/******************************************************************************
* Function Name: Userdef_OSTM1_WaitInt
* Description  : 
* Arguments    : 
* Return Value : none
******************************************************************************/
void Userdef_OSTM1_WaitInt(void)
{
}

/* End of File */

