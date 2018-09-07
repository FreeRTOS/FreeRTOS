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
* File Name    : r_cg_resetprg.c
* Version      : Code Generator for RX71M V1.00.02.02 [28 May 2015]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : CCRX
* Description  : Reset program.
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
#include <machine.h>
#include <_h_c_lib.h>
//#include <stddef.h> // Remove the comment when you use errno
//#include <stdlib.h> // Remove the comment when you use rand()
#include "r_cg_stacksct.h"
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif
void PowerON_Reset_PC(void);
void main(void);
#ifdef __cplusplus
}
#endif

#define PSW_init  0x00010000        /* PSW bit pattern */
#define FPSW_init 0x00000000        /* FPSW bit base pattern */

#pragma section ResetPRG            /* output PowerON_Reset_PC to PResetPRG section */

#pragma entry PowerON_Reset_PC

void PowerON_Reset_PC(void)
{
#ifdef __RXV2
    set_extb(__sectop("EXCEPTVECT"));
#endif
    set_intb(__sectop("C$VECT"));

#ifdef __ROZ                        /* Initialize FPSW */
#define _ROUND 0x00000001           /* Let FPSW RMbits=01 (round to zero) */
#else
#define _ROUND 0x00000000           /* Let FPSW RMbits=00 (round to nearest) */
#endif
#ifdef __DOFF
#define _DENOM 0x00000100           /* Let FPSW DNbit=1 (denormal as zero) */
#else
#define _DENOM 0x00000000           /* Let FPSW DNbit=0 (denormal as is) */
#endif

    set_fpsw(FPSW_init | _ROUND | _DENOM);

    _INITSCT();                     /* Initialize Sections */
    HardwareSetup();                /* Use Hardware Setup */
    nop();
    set_psw(PSW_init);              /* Set Ubit & Ibit for PSW */
    main();
    brk();
}
/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
