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
* File Name   : ostm.c
* $Rev: $
* $Date::                           $
* Description : Aragon Sample Program - OS timer device driver (Initialize process)
*******************************************************************************/

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "dev_drv.h"                /* Device Driver common header */
#include "devdrv_ostm.h"            /* OSTM Driver header */
#include "iodefine.h"

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/
/* ==== OSTM H/W ==== */
#define OSTM_CH_TOTAL       (2)

/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/

/******************************************************************************
Private global variables and functions
******************************************************************************/
static void OSTM_Open(volatile struct st_ostm_n * ostm);
static void OSTM_Close(volatile struct st_ostm_n * ostm, uint32_t * count);

/******************************************************************************
* Function Name: R_OSTM_Init
* Description  :
* Arguments    : uint32_t channel
*              : uint32_t mode
*              : uint32_t cycle
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_OSTM_Init(uint32_t channel, uint32_t mode, uint32_t cycle)
{
    int32_t ret;

    if ((channel >= OSTM_CH_TOTAL) || (mode > OSTM_MODE_COMPARE))
    {
        return DEVDRV_ERROR;
    }

    switch (channel)
    {
        case DEVDRV_CH_0:
            ret = Userdef_OSTM0_Init(mode, cycle);
        break;
        case DEVDRV_CH_1:
            ret = Userdef_OSTM1_Init(mode, cycle);
        break;
        default:
            ret = DEVDRV_ERROR;
        break;
    }

    return ret;
}

/******************************************************************************
* Function Name: R_OSTM_Open
* Description  :
* Arguments    : int32_t channel
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_OSTM_Open(uint32_t channel)
{
    if (channel >= OSTM_CH_TOTAL)
    {
        return DEVDRV_ERROR;
    }

    switch (channel)
    {
        case DEVDRV_CH_0:
            OSTM_Open(&OSTM0);
        break;
        case DEVDRV_CH_1:
            OSTM_Open(&OSTM1);
        break;
        default:
        break;
    }

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: R_OSTM_Close
* Description  :
* Arguments    : uint32_t channel
* Return Value : DEVDRV_SUCCESS
*              : DEVDRV_ERROR
******************************************************************************/
int32_t R_OSTM_Close(uint32_t channel, uint32_t * count)
{
    if (channel >= OSTM_CH_TOTAL)
    {
        return DEVDRV_ERROR;
    }

    switch (channel)
    {
        case DEVDRV_CH_0:
            OSTM_Close(&OSTM0, count);
        break;
        case DEVDRV_CH_1:
            OSTM_Close(&OSTM1, count);
        break;
        default:
        break;
    }

    return DEVDRV_SUCCESS;
}

/******************************************************************************
* Function Name: int_ostm0_interrupt
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
int32_t R_OSTM_Interrupt(uint32_t channel)
{
    if (channel >= OSTM_CH_TOTAL)
    {
        return DEVDRV_ERROR;
    }

    switch (channel)
    {
        case DEVDRV_CH_0:
            Userdef_OSTM0_Int();
        break;
        case DEVDRV_CH_1:
            Userdef_OSTM1_Int();
        break;
        default:
        break;
    }

    return DEVDRV_SUCCESS;
}

/*******************************************************************************
* Function Name: OSTM_Open
* Description  : This function opens OSTM.
* Arguments    : volatile struct st_scif_n * ostm
* Return Value : none
*******************************************************************************/
static void OSTM_Open(volatile struct st_ostm_n * ostm)
{
    ostm->OSTMnTS.BIT.OSTMnTS = 1;
}

/******************************************************************************
* Function Name: OSTM_Close
* Description  : This function closes OSTM.
* Arguments    : volatile struct st_scif_n * ostm
* Return Value : none
******************************************************************************/
static void OSTM_Close(volatile struct st_ostm_n * ostm, uint32_t * count)
{
    ostm->OSTMnTT.BIT.OSTMnTT = 1;
    *count = ostm->OSTMnCNT;
}

/* End of File */

