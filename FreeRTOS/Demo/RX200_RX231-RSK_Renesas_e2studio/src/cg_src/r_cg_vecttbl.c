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
* Version      : Code Generator for RX231 V1.00.00.03 [10 Jul 2015]
* Device(s)    : R5F52318AxFP
* Tool-Chain   : CCRX
* Description  : This file initializes the vector table.
* Creation Date: 23/09/2015
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

 
#define OFS0_VAL 0xFFFFFFFFUL
#define OFS1_VAL 0xFFFFFFFFUL

#pragma section C EXCEPTVECT
/* Start user code for adding. Do not edit comment generated here */
void (*const Excpt_Vectors[])(void) = {
/*;0xffffff80  MDE register */
#ifdef __BIG
    /* Big endian */
    (void (*)(void))0xfffffff8,
#else
    /* Little endian */
    (void (*)(void))0xffffffff,
#endif
/*;0xffffff84  Reserved */
    r_reserved_exception,
/*;0xffffff88  OFS1 register */
    (void (*) (void)) OFS1_VAL,
/*;0xffffff8c  OFS0 register */
    (void (*) (void)) OFS0_VAL,
/*;0xffffff90  Reserved */
    r_reserved_exception,
/*;0xffffff94  Reserved */
    r_reserved_exception,
/*;0xffffff98  Reserved */
    r_reserved_exception,
/*;0xffffff9c  Reserved */
    r_reserved_exception,
/*;0xffffffa0  ID */
    (void (*)(void))0xffffffff,
/*;0xffffffa4  ID */
    (void (*)(void))0xffffffff,
/*;0xffffffa8  ID */
    (void (*)(void))0xffffffff,
/*;0xffffffac  ID */
    (void (*)(void))0xffffffff,
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
/*;0xffffffd0  Exception(Privileged Instruction) */
    r_privileged_exception,
/*;0xffffffd4  Exception(Access) */
    r_access_exception,
/*;0xffffffd8  Reserved */
    r_reserved_exception,
/*;0xffffffdc  Exception(Undefined Instruction) */
    r_undefined_exception,
/*;0xffffffe0  Reserved */
    r_reserved_exception,
/*;0xffffffe4  Exception(Floating Point) */
    r_floatingpoint_exception,
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
/* End user code. Do not edit comment generated here */

#pragma section C RESETVECT
void (*const Reset_Vectors[])(void) = {
/*;<<VECTOR DATA START (POWER ON RESET)>> */
/*;Power On Reset PC */
    /*(void*)*/ PowerON_Reset_PC
/*;<<VECTOR DATA END (POWER ON RESET)>> */
};
