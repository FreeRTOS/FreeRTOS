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
/*******************************************************************************
* File Name    : port_init.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.8
*              : ARM Complier
* OS           :
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Initialize peripheral function sample
* Operation    :
* Limitations  :
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "devdrv_common.h"       /* Common Driver Header */
#include "port_init.h"
#include "iodefine.h"

/* Do not include the following pragmas when compiling with IAR. */
#ifndef __ICCARM__
	#pragma arm section code   = "CODE_RESET"
	#pragma arm section rodata = "CONST_RESET"
	#pragma arm section rwdata = "DATA_RESET"
	#pragma arm section zidata = "BSS_RESET"
#endif

/******************************************************************************
Typedef definitions
******************************************************************************/


/******************************************************************************
Macro definitions
******************************************************************************/


/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/


/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/


/******************************************************************************
Private global variables and functions
******************************************************************************/


/******************************************************************************
* Function Name: PORT_Init
* Description  :
*              :
*              :
* Arguments    : none
* Return Value : none
******************************************************************************/
void PORT_Init(void)
{
    /* ==== BSC settings ==== */

    /* ---- P7_2 : RAS# ---- */
    PORT7.PMCn.BIT.PMCn2     = 1;
    PORT7.PFCAEn.BIT.PFCAEn2 = 0;
    PORT7.PFCEn.BIT.PFCEn2   = 0;
    PORT7.PFCn.BIT.PFCn2     = 0;
    PORT7.PIPCn.BIT.PIPCn2   = 1;

    /* ---- P7_3 : CAS# ---- */
    PORT7.PMCn.BIT.PMCn3     = 1;
    PORT7.PFCAEn.BIT.PFCAEn3 = 0;
    PORT7.PFCEn.BIT.PFCEn3   = 0;
    PORT7.PFCn.BIT.PFCn3     = 0;
    PORT7.PIPCn.BIT.PIPCn3   = 1;

    /* ---- P7_4 : CKE ---- */
    PORT7.PMCn.BIT.PMCn4     = 1;
    PORT7.PFCAEn.BIT.PFCAEn4 = 0;
    PORT7.PFCEn.BIT.PFCEn4   = 0;
    PORT7.PFCn.BIT.PFCn4     = 0;
    PORT7.PIPCn.BIT.PIPCn4   = 1;

    /* ---- P7_5 : RD/WR# ---- */
    PORT7.PMCn.BIT.PMCn5     = 1;
    PORT7.PFCAEn.BIT.PFCAEn5 = 0;
    PORT7.PFCEn.BIT.PFCEn5   = 0;
    PORT7.PFCn.BIT.PFCn5     = 0;
    PORT7.PIPCn.BIT.PIPCn5   = 1;

    /* ---- P7_7 : DQMLU# ---- */
    PORT7.PMCn.BIT.PMCn7     = 1;
    PORT7.PFCAEn.BIT.PFCAEn7 = 0;
    PORT7.PFCEn.BIT.PFCEn7   = 0;
    PORT7.PFCn.BIT.PFCn7     = 0;
    PORT7.PIPCn.BIT.PIPCn7   = 1;

    /* ---- P5_8 : CS2 ---- */
    PORT5.PMCn.BIT.PMCn8     = 1;
    PORT5.PFCAEn.BIT.PFCAEn8 = 1;
    PORT5.PFCEn.BIT.PFCEn8   = 0;
    PORT5.PFCn.BIT.PFCn8     = 1;
    PORT5.PIPCn.BIT.PIPCn8   = 1;

    /* ---- P7_1 : CS3 ---- */
    PORT7.PMCn.BIT.PMCn1     = 1;
    PORT7.PFCAEn.BIT.PFCAEn1 = 0;
    PORT7.PFCEn.BIT.PFCEn1   = 0;
    PORT7.PFCn.BIT.PFCn1     = 0;
    PORT7.PIPCn.BIT.PIPCn1   = 1;
}

/* End of File */

