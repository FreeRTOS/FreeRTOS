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
* Version      : Code Generator for RX113 V1.02.01.02 [28 May 2015]
* Device(s)    : R5F51138AxFP
* Tool-Chain   : CCRX
* Description  : This file initializes the vector table.
* Creation Date: 21/09/2015
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

#pragma section C FIXEDVECT

void (*const Fixed_Vectors[])(void) = {
/*;0xffffffd0  Exception(Supervisor Instruction) */
    r_undefined_exception,
/*;0xffffffd4  Reserved */
    r_undefined_exception,
/*;0xffffffd8  Reserved */
    r_reserved_exception,
/*;0xffffffdc  Exception(Undefined Instruction) */
    r_undefined_exception,
/*;0xffffffe0  Reserved */
    r_reserved_exception,
/*;0xffffffe4  Reserved */
    r_reserved_exception,
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
/*;0xfffffffc  RESET */
/*;<<VECTOR DATA START (POWER ON RESET)>> */
/*;Power On Reset PC */
    /*(void*)*/ PowerON_Reset
/*;<<VECTOR DATA END (POWER ON RESET)>> */
};

/* MDE register (Single Chip Mode) */
#pragma address _MDEreg=0xffffff80
#ifdef __BIG
    /* Big endian*/
    const unsigned long _MDEreg = 0xfffffff8;
#else
    /* Little endian */
    const unsigned long _MDEreg = 0xffffffff;
#endif

/* Set option bytes */
#pragma address OFS0_location = 0xFFFFFF8CUL
#pragma address OFS1_location = 0xFFFFFF88UL
volatile const uint32_t OFS0_location = 0xFFFFFFFFUL;
volatile const uint32_t OFS1_location = 0xFFFFFFFFUL;

/* Start user code for adding. Do not edit comment generated here */
/* ID codes (Default) */
#pragma address id_code=0xffffffa0
const unsigned long id_code[4] = {
    0xffffffff,
    0xffffffff,
    0xffffffff,
    0xffffffff,
};
/* End user code. Do not edit comment generated here */

