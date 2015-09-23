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
* File Name    : r_cg_tpu.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for TPU module.
* Creation Date: 22/04/2015
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
#include "r_cg_tpu.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_TPU_Create
* Description  : This function initializes the TPU Unit0 module.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_TPU_Create(void)
{
    /* Cancel TPU stop state in LPC */
    MSTP(TPU1) = 0U;

    /* Stop all channels */
    TPUA.TSTRB.BYTE = 0x00U;

    /* Channel 9 is used as normal mode */
    TPU9.TCR.BYTE = _TPU_PCLKD_4096 | _TPU_CKEG_IT_R | _TPU_CKCL_DIS;
    TPU9.TIER.BYTE |= _TPU_TGIEA_DISABLE | _TPU_TGIEB_DISABLE | _TPU_TGIEC_DISABLE | _TPU_TGIED_DISABLE | 
                      _TPU_TCIEV_DISABLE | _TPU_TTGE_DISABLE;
    TPU9.TIORH.BYTE = _TPU_IOB_IR | _TPU_IOA_DISABLE;
    TPU9.TIORL.BYTE = _TPU_IOD_IR | _TPU_IOC_IR;
    TPU9.TGRA = _TPU9_TCNTA_VALUE;
    TPU9.TMDR.BYTE = _TPU_NORMAL | _TPU_BFA_NORMAL | _TPU_BFB_NORMAL | _TPU_ICSELB_BPIN | _TPU_ICSELD_DPIN;

    /* Internal PWM feedback function status */
    TPUSL.PWMFBSLR.LONG = _TPU_TPU0EN_DISABLE | _TPU_TPU1EN_DISABLE;
}
/***********************************************************************************************************************
* Function Name: R_TPU9_Start
* Description  : This function starts TPU channel 9 counter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_TPU9_Start(void)
{
    TPUA.TSTRB.BIT.CST3 = 1U;
}
/***********************************************************************************************************************
* Function Name: R_TPU9_Stop
* Description  : This function stops TPU channel 9 counter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_TPU9_Stop(void)
{
    TPUA.TSTRB.BIT.CST3 = 0U;
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
