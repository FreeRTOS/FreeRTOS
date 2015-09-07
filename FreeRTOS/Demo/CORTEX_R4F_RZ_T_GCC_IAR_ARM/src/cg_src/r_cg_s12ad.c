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
* File Name    : r_cg_s12ad.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for S12AD module.
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
#include "r_cg_s12ad.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_S12AD0_Create
* Description  : This function initializes the AD0 converter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_S12AD0_Create(void)
{
    /* Cancel S12ADC0 module stop state */
    MSTP(S12ADC0) = 0U;

    /* Disable and clear S12ADI0, S12GBADI0, S12CMPI0 interrupt flags */
    S12ADC0.ADCSR.BIT.ADIE = 0U;
    S12ADC0.ADCSR.BIT.GBADIE = 0U;
    S12ADC0.ADCMPCR.BIT.CMPIE = 0U;
    VIC.IEC1.LONG = 0x00000008UL;

    /* Set S12AD0 control registers */
    S12ADC0.ADDISCR.BYTE = _AD0_DISCONECT_SETTING;
    S12ADC0.ADCSR.WORD = _AD_DBLTRIGGER_DISABLE | _AD_SCAN_END_INTERRUPT_ENABLE | _AD_SINGLE_SCAN_MODE;
    S12ADC0.ADCER.WORD = _AD_AUTO_CLEARING_DISABLE | _AD_RIGHT_ALIGNMENT | _AD_RESOLUTION_12BIT;
    S12ADC0.ADADC.BYTE = _AD_1_TIME_CONVERSION | _AD_ADDITION_MODE;

    /* Set channels and sampling time */
    S12ADC0.ADANSA.WORD = _AD0_CHANNEL_SELECT_A;
    S12ADC0.ADADS.WORD = _AD0_ADDAVG_CHANNEL_SELECT;
    S12ADC0.ADSSTR7.BYTE = _AD0_SAMPLING_STATE_7;

    /* Set compare control register */
    S12ADC0.ADCMPCR.BYTE = _AD_WINDOWFUNCTION_DISABLE;
    S12ADC0.ADCMPANSR.WORD = _AD0_COMPARECHANNEL_SELECT;
    S12ADC0.ADCMPLR.WORD = _AD0_COMPARELEVEL_SELECT;
    S12ADC0.ADCMPDR0 = 0x0000U;

    /* Set S12ADI0 edge detection type */
    VIC.PLS1.LONG |= 0x00000008UL;

    /* Set S12ADI0 interrupt priority level */
    VIC.PRL35.LONG = _AD_PRIORITY_LEVEL0;

    /* Set S12ADI0 interrupt address */
    VIC.VAD35.LONG = (uint32_t)r_s12ad_s12adi0_interrupt;

}
/***********************************************************************************************************************
* Function Name: R_S12AD0_Start
* Description  : This function starts the AD0 converter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_S12AD0_Start(void)
{
    /* Enable S12ADI0 interrupt in ICU */
    VIC.IEN1.LONG |= 0x00000008UL;

    S12ADC0.ADCSR.BIT.ADST = 1U;
}
/***********************************************************************************************************************
* Function Name: R_S12AD0_Stop
* Description  : This function stops the AD0 converter.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_S12AD0_Stop(void)
{
    S12ADC0.ADCSR.BIT.ADST = 0U;

    /* Disable S12ADI0 interrupt in ICU */
    VIC.IEC1.LONG = 0x00000008UL;
}
/***********************************************************************************************************************
* Function Name: R_S12AD0_Get_ValueResult
* Description  : This function gets result from the AD0 converter.
* Arguments    : channel -
*                    channel of data register to be read
*                buffer -
*                    buffer pointer
* Return Value : None
***********************************************************************************************************************/
void R_S12AD0_Get_ValueResult(ad_channel_t channel, uint16_t * const buffer)
{
    if (channel == ADSELFDIAGNOSIS)
    {
        *buffer = (uint16_t)(S12ADC0.ADRD);
    }
    else if (channel == ADCHANNEL0)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR0);
    }
    else if (channel == ADCHANNEL1)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR1);
    }
    else if (channel == ADCHANNEL2)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR2);
    }
    else if (channel == ADCHANNEL3)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR3);
    }
    else if (channel == ADCHANNEL4)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR4);
    }
    else if (channel == ADCHANNEL5)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR5);
    }
    else if (channel == ADCHANNEL6)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR6);
    }
    else if (channel == ADCHANNEL7)
    {
        *buffer = (uint16_t)(S12ADC0.ADDR7);
    }
    else if (channel == ADTEMPSENSOR)
    {
        *buffer = (uint16_t)(S12ADC0.ADTSDR);
    }
    else if (channel == ADDATADUPLICATION)
    {
        *buffer = (uint16_t)(S12ADC0.ADDBLDR);
    }
    else if (channel == ADDATADUPLICATIONA)
    {
        *buffer = (uint16_t)(S12ADC0.ADDBLDRA);
    }
    else if (channel == ADDATADUPLICATIONB)
    {
        *buffer = (uint16_t)(S12ADC0.ADDBLDRB);
    }
}
/***********************************************************************************************************************
* Function Name: R_S12AD0_Set_CompareValue
* Description  : This function sets reference data for AD0 comparison.
* Arguments    : reg_value0 -
*                    reference data 0 for comparison
*                reg_value1 -
*                    reference data 1 for comparison
* Return Value : None
***********************************************************************************************************************/
void R_S12AD0_Set_CompareValue(uint16_t reg_value0, uint16_t reg_value1 )
{
     S12ADC0.ADCMPDR0 = reg_value0;
     S12ADC0.ADCMPDR1 = reg_value1;
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
