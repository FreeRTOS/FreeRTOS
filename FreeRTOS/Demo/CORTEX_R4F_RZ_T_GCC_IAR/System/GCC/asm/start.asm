/************************************************************************************************************************
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
************************************************************************************************************************/
/************************************************************************************************************************
* File Name     : start.asm
* Device(s)     : RZ/T1 (R7S910018)
* Tool-Chain    : GNUARM-NONEv14.02-EABI
* H/W Platform  : RSK+T1 CPU Board
* Description   : This is the code to be executed on the target
                  The copyright string signifies the end of the Vector table
*                 Note boot strap sequence is as follows:
*
*                 start->reset_handler->main()
*
*                 start - first code to be executed on the target
                  start jumps to reset_handler the asm startup routine
*                 reset_handler jumps to loader_init1() C entry point
*                 loader_init2() calls main() C User code entry point
************************************************************************************************************************/
/************************************************************************************************************************
* History       : DD.MM.YYYY Version Description
*               : 21.05.2015 1.00
************************************************************************************************************************/

    .text
    .code 32

	.extern FreeRTOS_SVC_Handler
    .global start
    .func   start

start:
    LDR pc, =reset_handler                  /* Reset Vector                                  */
    LDR pc, =undefined_handler
    LDR pc, =FreeRTOS_SVC_Handler
    LDR pc, =prefetch_handler
    LDR pc, =abort_handler
    LDR pc, =reserved_handler
    LDR pc, =irq_handler
    LDR pc, =fiq_handler
code_start:
    .word    start                         /* pointer to the user application start address */
                                           /* Used by NOR and SPI (System_Boot_Loader_xxxx)  */
code_end:
    .word    end
code_execute:
    .word    execute                       /* execute address of first instruction          */
    .string ".BootLoad_ValidProgramTest."  /* bootloader validation signature               */
    .align 4
    .end
