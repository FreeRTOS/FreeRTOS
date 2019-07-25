/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_vecttbl.c
* Version      : Code Generator for RX71M V1.00.02.02 [28 May 2015]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : CCRX
* Description  : This file initializes the vector table.
* Creation Date: 20/09/2015
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_vect.h"
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/

#pragma section C EXCEPTVECT

void (*const Excpt_Vectors[])(void) = {
/*;0xffffff80  Reserved */
    r_reserved_exception,
/*;0xffffff84  Reserved */
    r_reserved_exception,
/*;0xffffff88  Reserved */
    r_reserved_exception,
/*;0xffffff8c  Reserved */
    r_reserved_exception,
/*;0xffffff90  Reserved */
    r_reserved_exception,
/*;0xffffff94  Reserved */
    r_reserved_exception,
/*;0xffffff98  Reserved */
    r_reserved_exception,
/*;0xffffff9c  Reserved */
    r_reserved_exception,
/*;0xffffffa0  Reserved */
    r_reserved_exception,
/*;0xffffffa4  Reserved */
    r_reserved_exception,
/*;0xffffffa8  Reserved */
    r_reserved_exception,
/*;0xffffffac  Reserved */
    r_reserved_exception,
/*;0xffffffb0  Reserved */
    r_reserved_exception,
/*;0xffffffb4  Reserved */
    r_reserved_exception,
/*;0xffffffb8  Reserved */
    r_reserved_exception,
/*;0xffffffbc  Reserved */
    r_reserved_exception,
/*;0xffffffc0  Reserved */
    r_reserved_exception,
/*;0xffffffc4  Reserved */
    r_reserved_exception,
/*;0xffffffc8  Reserved */
    r_reserved_exception,
/*;0xffffffcc  Reserved */
    r_reserved_exception,
/*;0xffffffd0  Exception(Supervisor Instruction) */
    r_undefined_exception,
/*;0xffffffd4  Reserved */
    r_reserved_exception,
/*;0xffffffd8  Reserved */
    r_reserved_exception,
/*;0xffffffdc  Exception(Undefined Instruction) */
    r_undefined_exception,
/*;0xffffffe0  Reserved */
    r_reserved_exception,
/*;0xffffffe4  Exception(Floating Point) */
    r_undefined_exception,
/*;0xffffffe8  Reserved */
    r_reserved_exception,
/*;0xffffffec  Reserved */
    r_reserved_exception,
/*;0xfffffff0  Reserved */
    r_reserved_exception,
/*;0xfffffff4  Reserved */
    r_reserved_exception,
/*;0xfffffff8  NMI */
    r_nmi_exception,
};

#pragma section C RESETVECT
void (*const Reset_Vectors[])(void) = {
/*;<<VECTOR DATA START (POWER ON RESET)>> */
/*;Power On Reset PC */
    /*(void*)*/ PowerON_Reset_PC
/*;<<VECTOR DATA END (POWER ON RESET)>> */
};

/* MDE register (Single Chip Mode) */
#pragma address __MDEreg=0x00120064
#ifdef __BIG
    /* Big endian*/
    const unsigned long __MDEreg = 0xFFFFFFF8;
#else
    /* Little endian */
    const unsigned long __MDEreg = 0xFFFFFFFF;
#endif

/* Set option bytes */
/* OFS0 register */
#pragma address __OFS0reg = 0x00120068
const unsigned long __OFS0reg = 0xFFFFFFFF;

/* OFS1 register */
#pragma address __OFS1reg = 0x0012006C              
const unsigned long __OFS1reg = 0xFFFFFFFF;

/* Start user code for adding. Do not edit comment generated here */
/* SPCC register */
#pragma address __SPCCreg=0x00120040
const unsigned long __SPCCreg = 0xffffffff;

/* TMEF register */
#pragma address __TMEFreg=0x00120048
const unsigned long __TMEFreg = 0xffffffff; 

/* OSIC register (ID codes) */
#pragma address __OSISreg=0x00120050
const unsigned long __OSISreg[4] = {
    0xFFFFFFFF,
    0xFFFFFFFF,
    0xFFFFFFFF,
    0xFFFFFFFF,
};

/* TMINF register */
#pragma address __TMINFreg=0x00120060
const unsigned long __TMINFreg = 0xffffffff;
/* End user code. Do not edit comment generated here */

