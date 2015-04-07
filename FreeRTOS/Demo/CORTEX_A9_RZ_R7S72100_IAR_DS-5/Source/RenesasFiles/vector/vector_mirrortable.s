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
;* File Name     : vector_mirrortable.s
;* Version       : 0.01
;* Device(s)     : Aragon
;* Tool-Chain    : DS-5 Ver 5.13
;*                 ARM Complier 
;*               : 
;* H/W Platform  : Aragon CPU Board
;* Description   : Aragon Sample Program - Vector mirrortable
;*******************************************************************************/
;/*******************************************************************************
;* History : DD.MM.YYYY Version Description
;*         : 23.05.2012 0.01
;*******************************************************************************/

;==================================================================
; Entry point for the Reset handler
;==================================================================
	PRESERVE8
	AREA VECTOR_MIRROR_TABLE, CODE, READONLY

;	EXPORT vector_table

	IMPORT  reset_handler
	IMPORT  undefined_handler
	IMPORT  prefetch_handler
	IMPORT  abort_handler
	IMPORT  reserved_handler
	IMPORT  FreeRTOS_IRQ_Handler
	IMPORT  fiq_handler
	IMPORT  FreeRTOS_SWI_Handler

;	ENTRY

;	EXPORT Start

;Start

vector_table2
	LDR pc, =reset_handler         ; 0x0000_0000
	LDR pc, =undefined_handler     ; 0x0000_0004
	LDR pc, =FreeRTOS_SWI_Handler  ; 0x0000_0008
	LDR pc, =prefetch_handler      ; 0x0000_000c
	LDR pc, =abort_handler         ; 0x0000_0010
	LDR pc, =reserved_handler      ; 0x0000_0014
	LDR pc, =FreeRTOS_IRQ_Handler  ; 0x0000_0018
	LDR pc, =fiq_handler           ; 0x0000_001c

Literals
	LTORG

	END
