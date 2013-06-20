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
;* File Name     : vbar_init.s
;* Version       : 0.01
;* Device(s)     : Aragon
;* Tool-Chain    : DS-5 Ver 5.8
;*                 ARM Complier 
;*               : 
;* H/W Platform  : Aragon CPU Board
;* Description   : Aragon Sample Program
;*******************************************************************************/
;/*******************************************************************************
;* History : DD.MM.YYYY Version Description
;*         : 23.05.2012 0.01
;*******************************************************************************/

;==================================================================
; This code provides basic global enable for Cortex-A9 cache.
; It also enables branch prediction
; This code must be run from a privileged mode
;==================================================================
	AREA   INIT_VBAR, CODE, READONLY
	
	IMPORT  ||Image$$VECTOR_MIRROR_TABLE$$Base||
;	IMPORT  ||Image$$VECTOR_TABLE$$Base||
	
	EXPORT	VbarInit

VbarInit	FUNCTION

;===================================================================
; Set Vector Base Address Register (VBAR) to point to this application's vector table
;===================================================================
	LDR r0, =||Image$$VECTOR_MIRROR_TABLE$$Base||
;	LDR r0, =||Image$$VECTOR_TABLE$$Base||
	MCR p15, 0, r0, c12, c0, 0

	BX		lr

	ENDFUNC




	END
