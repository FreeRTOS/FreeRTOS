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
* File Name    : r_cg_sci.c
* Version      : Code Generator for RX71M V1.00.02.02 [28 May 2015]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : CCRX
* Description  : This file implements device driver for SCI module.
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
#include "r_cg_sci.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
uint8_t * gp_sci7_tx_address;               /* SCI7 transmit buffer address */
uint16_t  g_sci7_tx_count;                  /* SCI7 transmit data number */
uint8_t * gp_sci7_rx_address;               /* SCI7 receive buffer address */
uint16_t  g_sci7_rx_count;                  /* SCI7 receive data number */
uint16_t  g_sci7_rx_length;                 /* SCI7 receive data length */
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_SCI7_Create
* Description  : This function initializes SCI7.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCI7_Create(void)
{
    /* Cancel SCI7 module stop state */
    MSTP(SCI7) = 0U;

    /* Set interrupt priority */
    IPR(SCI7, RXI7) = _0F_SCI_PRIORITY_LEVEL15;
    IPR(SCI7, TXI7) = _0F_SCI_PRIORITY_LEVEL15;

    /* Clear the control register */
    SCI7.SCR.BYTE = 0x00U;

    /* Set clock enable */
    SCI7.SCR.BYTE = _00_SCI_INTERNAL_SCK_UNUSED;

    /* Clear the SIMR1.IICM, SPMR.CKPH, and CKPOL bit, and set SPMR */
    SCI7.SIMR1.BIT.IICM = 0U;
    SCI7.SPMR.BYTE = _00_SCI_RTS | _00_SCI_CLOCK_NOT_INVERTED | _00_SCI_CLOCK_NOT_DELAYED;

    /* Set control registers */
    SCI7.SMR.BYTE = _00_SCI_CLOCK_PCLK | _00_SCI_STOP_1 | _00_SCI_PARITY_EVEN | _00_SCI_PARITY_DISABLE | 
                    _00_SCI_DATA_LENGTH_8 | _00_SCI_MULTI_PROCESSOR_DISABLE | _00_SCI_ASYNCHRONOUS_MODE;
    SCI7.SCMR.BYTE = _00_SCI_SERIAL_MODE | _00_SCI_DATA_INVERT_NONE | _00_SCI_DATA_LSB_FIRST | 
                     _10_SCI_DATA_LENGTH_8_OR_7 | _62_SCI_SCMR_DEFAULT;
    SCI7.SEMR.BYTE = _80_SCI_FALLING_EDGE_START_BIT | _00_SCI_NOISE_FILTER_DISABLE | _10_SCI_8_BASE_CLOCK | 
                     _00_SCI_BAUDRATE_SINGLE | _00_SCI_BIT_MODULATION_DISABLE;

    /* Set bitrate */
    SCI7.BRR = 0xC2U;

    /* Set RXD7 pin */
    MPC.P92PFS.BYTE = 0x0AU;
    PORT9.PMR.BYTE |= 0x04U;

    /* Set TXD7 pin */
    MPC.P90PFS.BYTE = 0x0AU;
    PORT9.PODR.BYTE |= 0x01U;
    PORT9.PDR.BYTE |= 0x01U;
    PORT9.PMR.BYTE |= 0x01U;
}
/***********************************************************************************************************************
* Function Name: R_SCI7_Start
* Description  : This function starts SCI7.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCI7_Start(void)
{
    /* Clear interrupt flag */
    IR(SCI7, TXI7) = 0U;
    IR(SCI7, RXI7) = 0U;

    /* Enable SCI interrupt */
    IEN(SCI7, TXI7) = 1U;
    ICU.GENBL0.BIT.EN14 = 1U;
    IEN(SCI7, RXI7) = 1U;
    ICU.GENBL0.BIT.EN15 = 1U;
}
/***********************************************************************************************************************
* Function Name: R_SCI7_Stop
* Description  : This function stops SCI7.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCI7_Stop(void)
{
    /* Set TXD7 pin */
    PORT9.PMR.BYTE &= 0xFEU;
    SCI7.SCR.BIT.TE = 0U;      /* Disable serial transmit */
    SCI7.SCR.BIT.RE = 0U;      /* Disable serial receive */

    /* Disable SCI interrupt */
    SCI7.SCR.BIT.TIE = 0U;     /* Disable TXI interrupt */
    SCI7.SCR.BIT.RIE = 0U;     /* Disable RXI and ERI interrupt */
    IR(SCI7, TXI7) = 0U;
    IEN(SCI7, TXI7) = 0U;
    ICU.GENBL0.BIT.EN14 = 0U;
    IR(SCI7, RXI7) = 0U;
    IEN(SCI7, RXI7) = 0U;
    ICU.GENBL0.BIT.EN15 = 0U;
}
/***********************************************************************************************************************
* Function Name: R_SCI7_Serial_Receive
* Description  : This function receives SCI7 data.
* Arguments    : rx_buf -
*                    receive buffer pointer (Not used when receive data handled by DTC or DMAC)
*                rx_num -
*                    buffer size (Not used when receive data handled by DTC or DMAC)
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCI7_Serial_Receive(uint8_t * const rx_buf, uint16_t rx_num)
{
    MD_STATUS status = MD_OK;

    if (1U > rx_num)
    {
        status = MD_ARGERROR;
    }
    else
    {
        g_sci7_rx_count = 0U;
        g_sci7_rx_length = rx_num;
        gp_sci7_rx_address = rx_buf;
        SCI7.SCR.BIT.RIE = 1U;
        SCI7.SCR.BIT.RE = 1U;
    }

    return (status);
}
/***********************************************************************************************************************
* Function Name: R_SCI7_Serial_Send
* Description  : This function transmits SCI7 data.
* Arguments    : tx_buf -
*                    transfer buffer pointer (Not used when transmit data handled by DTC)
*                tx_num -
*                    buffer size (Not used when transmit data handled by DTC or DMAC)
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCI7_Serial_Send(uint8_t * const tx_buf, uint16_t tx_num)
{
    MD_STATUS status = MD_OK;

    if (1U > tx_num)
    {
        status = MD_ARGERROR;
    }
    else
    {
        gp_sci7_tx_address = tx_buf;
        g_sci7_tx_count = tx_num;

        /* Set TXD7 pin */
        PORT9.PMR.BYTE |= 0x01U;
        SCI7.SCR.BIT.TIE = 1U;
        SCI7.SCR.BIT.TE = 1U;
    }

    return (status);
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
