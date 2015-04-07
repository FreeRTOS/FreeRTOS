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
* File Name   : scif_uart_initialize.c
* $Rev: $
* $Date::                           $
* Description : Aragon Sample Program - SCIF UART device driver (Initialize process)
*******************************************************************************/

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "dev_drv.h"                /* Device Driver common header */
#include "devdrv_scif_uart.h"       /* UART Driver header */
#include "iodefine.h"

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/
#define SCIF_UART_CH_TOTAL      (8)

/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/

/******************************************************************************
Private global variables and functions
******************************************************************************/

/******************************************************************************
* Function Name: R_SCIF_UART_Init
* Description  :
* Arguments    : uint32_t channel
*              : uint32_t mode
*              :                  :   SCIF_UART_MODE_W
*              :                  :   SCIF_UART_MODE_R
*              :                  :   SCIF_UART_MODE_RW
*              : uint16_t cks
*              : uint8_t scbrr
* Return Value : DEVDRV_SUCCESS   : Success
*              : DEVDRV_ERROR     : Error
******************************************************************************/
int32_t R_SCIF_UART_Init(uint32_t channel, uint32_t mode, uint16_t cks, uint8_t scbrr)
{
    if ((channel >= SCIF_UART_CH_TOTAL) || (mode < SCIF_UART_MODE_W) || (mode > SCIF_UART_MODE_RW) || (cks > 3))
    {
        return DEVDRV_ERROR;
    }

    switch (channel)
    {
        case DEVDRV_CH_2:
            Userdef_SCIF2_UART_Init(mode, cks, scbrr);
        break;
        default:
            /* Do Nothing */
        break;
    }

    return DEVDRV_SUCCESS;
}

/* End of File */

