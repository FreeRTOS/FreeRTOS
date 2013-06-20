;/*******************************************************************************
;* DISCLAIMER
;* This software is supplied by Renesas Electronics Corporation and is only
;* intended for use with Renesas products. No other uses are authorized. This
;* software is owned by Renesas Electronics Corporation and is protected under
;* all applicable laws, including copyright laws.
;* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
;* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
;* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
;* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
;* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
;* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
;* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
;* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
;* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
;* Renesas reserves the right, without notice, to make changes to this software
;* and to discontinue the availability of this software. By using this software,
;* you agree to the additional terms and conditions found by accessing the
;* following link:
;* http://www.renesas.com/disclaimer
;*
;* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
;*******************************************************************************/
;/*******************************************************************************
;* File Name     : irqfiq_handler.s
;* Version       : 0.01
;* Device(s)     : Aragon
;* Tool-Chain    : DS-5 Ver 5.13
;*                 ARM Complier
;*               :
;* H/W Platform  : Aragon CPU Board
;* Description   : Aragon Sample Program - IRQ, FIQ handler
;*******************************************************************************/
;/*******************************************************************************
;* History : DD.MM.YYYY Version Description
;*         : 23.05.2012 0.01
;*******************************************************************************/

; Standard definitions of mode bits and interrupt (I & F) flags in PSRs
INTC_ICCIAR_ADDR    EQU 	0xE820200C
INTC_ICCEOIR_ADDR   EQU 	0xE8202010


;==================================================================
; Entry point for the FIQ handler
;==================================================================
	PRESERVE8
	AREA IRQ_FIQ_HANDLER, CODE, READONLY

	IMPORT	FiqHandler_Interrupt

	EXPORT  fiq_handler

fiq_handler
	BL	FiqHandler_Interrupt

fiq_handler_end
	B	fiq_handler_end


Literals3
	LTORG

	END
