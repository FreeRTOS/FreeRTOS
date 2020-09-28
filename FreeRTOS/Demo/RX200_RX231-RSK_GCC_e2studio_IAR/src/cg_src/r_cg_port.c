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
* File Name    : r_cg_port.c
* Version      : Code Generator for RX231 V1.00.00.03 [10 Jul 2015]
* Device(s)    : R5F52318AxFP
* Tool-Chain   : CCRX
* Description  : This file implements device driver for Port module.
* Creation Date: 2015/08/17
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
#include "r_cg_port.h"
/* Start user code for include. Do not edit comment generated here */
#include "rskrx231def.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */

#if defined(RSK_RX231)

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_PORT_Create
* Description  : This function initializes the Port I/O.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_PORT_Create(void)
{
    PORT1.PODR.BYTE = _80_Pm7_OUTPUT_1;
    PORT3.PODR.BYTE = _08_Pm3_OUTPUT_1;
    PORT5.PODR.BYTE = _01_Pm0_OUTPUT_1 | _02_Pm1_OUTPUT_1 | _04_Pm2_OUTPUT_1;
    PORTE.PODR.BYTE = _08_Pm3_OUTPUT_1 | _80_Pm7_OUTPUT_1;
    PORT1.PDR.BYTE = _80_Pm7_MODE_OUTPUT;
    PORT3.PDR.BYTE = _08_Pm3_MODE_OUTPUT;
    PORT5.PDR.BYTE = _01_Pm0_MODE_OUTPUT | _02_Pm1_MODE_OUTPUT | _04_Pm2_MODE_OUTPUT;
    PORTE.PDR.BYTE = _08_Pm3_MODE_OUTPUT | _10_Pm4_MODE_OUTPUT | _80_Pm7_MODE_OUTPUT;
}

/* Start user code for adding. Do not edit comment generated here */

#elif defined(TB_RX231)

void R_PORT_Create(void)
{
    PORTD.PODR.BYTE = _40_Pm6_OUTPUT_1 | _80_Pm7_OUTPUT_1;
    PORTD.PDR.BYTE = _40_Pm6_MODE_OUTPUT | _80_Pm7_MODE_OUTPUT;
}

#endif

/* End user code. Do not edit comment generated here */
