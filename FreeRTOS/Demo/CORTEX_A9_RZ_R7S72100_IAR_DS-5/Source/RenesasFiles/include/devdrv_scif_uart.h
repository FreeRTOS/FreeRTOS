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
/******************************************************************************
* File Name    : scif_uart.h
* $Rev: $
* $Date::                           $
* Description  : Aragon Sample Program - SCIF UART device driver header
******************************************************************************/
#ifndef _DEVDRV_SCIF_UART_H_
#define _DEVDRV_SCIF_UART_H_

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "iodefine.h"

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/
#define SCIF_UART_MODE_W        (1)
#define SCIF_UART_MODE_R        (2)
#define SCIF_UART_MODE_RW       (3)

typedef enum scif_cks_division
{
    SCIF_CKS_DIVISION_1,
    SCIF_CKS_DIVISION_4,
    SCIF_CKS_DIVISION_16,
    SCIF_CKS_DIVISION_64
} scif_cks_division_t;

/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/
int32_t R_SCIF_UART_Init(uint32_t channel, uint32_t mode, uint16_t cks, uint8_t scbrr);

void Userdef_SCIF2_UART_Init(uint8_t mode, uint16_t cks, uint8_t scbrr);

#endif  /* _DEVDRV_SCIF_UART_H_ */

/* End of File */
