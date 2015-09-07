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
 System Name  : RZ/T1 Init program
 File Name    : vector.asm
 Version      : 0.1
 Device       : R7S910018
 Abstract     : vector address (in low vector)
 Tool-Chain   : GNUARM-NONEv14.02-EABI
 OS           : not use
 H/W Platform : Renesas Starter Kit for RZ/T1
 Description  : vector address for RZ/T1 (in low vector)
 Limitation   : none
***********************************************************************************************************************/
/***********************************************************************************************************************
* History      : DD.MM.YYYY Version  Description
*              : 21.05.2015 1.00     First Release
***********************************************************************************************************************/

/* This program is allocated to section "intvec" */ 

    .text
    .code 32

    .global undefined_handler
    .global FreeRTOS_SVC_Handler
    .global prefetch_handler
    .global abort_handler
    .global reserved_handler
    .global irq_handler
    .global fiq_handler
    

undefined_handler:
    b  undefined_handler

svc_handler:
    b  svc_handler

prefetch_handler:
    b  prefetch_handler

abort_handler:
    b  abort_handler

reserved_handler:
    b  reserved_handler

irq_handler:
    b  irq_handler

fiq_handler:
    b  fiq_handler

    .end

