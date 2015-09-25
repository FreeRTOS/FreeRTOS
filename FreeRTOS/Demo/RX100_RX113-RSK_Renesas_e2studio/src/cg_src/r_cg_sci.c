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
* Version      : Code Generator for RX113 V1.02.01.02 [28 May 2015]
* Device(s)    : R5F51138AxFP
* Tool-Chain   : CCRX
* Description  : This file implements device driver for SCI module.
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
#include "r_cg_sci.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
uint8_t * gp_sci1_tx_address;         /* SCI1 transmit buffer address */
uint16_t  g_sci1_tx_count;            /* SCI1 transmit data number */
uint8_t * gp_sci1_rx_address;         /* SCI1 receive buffer address */
uint16_t  g_sci1_rx_count;            /* SCI1 receive data number */
uint16_t  g_sci1_rx_length;           /* SCI1 receive data length */
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_SCI1_Create
* Description  : This function initializes the SCI1.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCI1_Create(void)
{
    /* Cancel SCI1 module stop state */
    MSTP(SCI1) = 0U;

    /* Set interrupt priority */
    IPR(SCI1, ERI1) = _0F_SCI_PRIORITY_LEVEL15;

    /* Clear the SCR.TIE, RIE, TE, RE and TEIE bits */
    SCI1.SCR.BIT.TIE = 0U;
    SCI1.SCR.BIT.RIE = 0U;
    SCI1.SCR.BIT.TE = 0U;
    SCI1.SCR.BIT.RE = 0U;
    SCI1.SCR.BIT.TEIE = 0U;

    /* Set RXD1 pin */
    MPC.P15PFS.BYTE = 0x0AU;
    PORT1.PMR.BYTE |= 0x20U;
    /* Set TXD1 pin */
    MPC.P16PFS.BYTE = 0x0AU;
    PORT1.PODR.BYTE |= 0x40U;
    PORT1.PDR.BYTE |= 0x40U;
    PORT1.PMR.BYTE |= 0x40U;

    /* Set clock enable */
    SCI1.SCR.BYTE = _00_SCI_INTERNAL_SCK_UNUSED;

    /* Clear the SIMR1.IICM, SPMR.CKPH, and CKPOL bit */
    SCI1.SIMR1.BIT.IICM = 0U;
    SCI1.SPMR.BYTE = _00_SCI_RTS | _00_SCI_CLOCK_NOT_INVERTED | _00_SCI_CLOCK_NOT_DELAYED;

    /* Set control registers */
    SCI1.SMR.BYTE = _01_SCI_CLOCK_PCLK_4 | _00_SCI_STOP_1 | _00_SCI_PARITY_EVEN | _00_SCI_PARITY_DISABLE | 
                    _00_SCI_DATA_LENGTH_8 | _00_SCI_MULTI_PROCESSOR_DISABLE | _00_SCI_ASYNCHRONOUS_MODE;
    SCI1.SCMR.BYTE = _00_SCI_SERIAL_MODE | _00_SCI_DATA_INVERT_NONE | _00_SCI_DATA_LSB_FIRST | _72_SCI_SCMR_DEFAULT;

    /* Set SEMR, SNFR */
    SCI1.SEMR.BYTE = _00_SCI_LOW_LEVEL_START_BIT | _00_SCI_NOISE_FILTER_DISABLE | _10_SCI_8_BASE_CLOCK;

    /* Set bitrate */
    SCI1.BRR = 0x19U;
}
/***********************************************************************************************************************
* Function Name: R_SCI1_Start
* Description  : This function starts the SCI1.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCI1_Start(void)
{
    IR(SCI1,TXI1) = 0U;
    IR(SCI1,TEI1) = 0U;
    IR(SCI1,RXI1) = 0U;
    IR(SCI1,ERI1) = 0U;
    IEN(SCI1,TXI1) = 1U;
    IEN(SCI1,TEI1) = 1U;
    IEN(SCI1,RXI1) = 1U;
    IEN(SCI1,ERI1) = 1U;
}
/***********************************************************************************************************************
* Function Name: R_SCI1_Stop
* Description  : This function stops the SCI1.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCI1_Stop(void)
{
    /* Set TXD1 pin */
    PORT1.PMR.BYTE &= 0xBFU;

    SCI1.SCR.BYTE &= 0xCF;    /* Disable serial transmit and receive */
    SCI1.SCR.BIT.TIE = 0U;    /* Disable TXI interrupt */
    SCI1.SCR.BIT.RIE = 0U;    /* Disable RXI and ERI interrupt */
    IR(SCI1,TXI1) = 0U;
    IEN(SCI1,TXI1) = 0U;
    IR(SCI1,TEI1) = 0U;
    IEN(SCI1,TEI1) = 0U;
    IR(SCI1,RXI1) = 0U;
    IEN(SCI1,RXI1) = 0U;
    IR(SCI1,ERI1) = 0U;
    IEN(SCI1,ERI1) = 0U;
}
/***********************************************************************************************************************
* Function Name: R_SCI1_Serial_Receive
* Description  : This function receives SCI1 data.
* Arguments    : rx_buf -
*                    receive buffer pointer (Not used when receive data handled by DTC)
*                rx_num -
*                    buffer size
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCI1_Serial_Receive(uint8_t * const rx_buf, uint16_t rx_num)
{
    MD_STATUS status = MD_OK;

    if (rx_num < 1U)
    {
        status = MD_ARGERROR;
    }
    else
    {
        g_sci1_rx_count = 0U;
        g_sci1_rx_length = rx_num;
        gp_sci1_rx_address = rx_buf;
        SCI1.SCR.BIT.RIE = 1U;
        SCI1.SCR.BIT.RE = 1U;
    }

    return (status);
}
/***********************************************************************************************************************
* Function Name: R_SCI1_Serial_Send
* Description  : This function transmits SCI1 data.
* Arguments    : tx_buf -
*                    transfer buffer pointer (Not used when transmit data handled by DTC)
*                tx_num -
*                    buffer size
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCI1_Serial_Send(uint8_t * const tx_buf, uint16_t tx_num)
{
    MD_STATUS status = MD_OK;

    if (tx_num < 1U)
    {
        status = MD_ARGERROR;
    }
    else
    {
        gp_sci1_tx_address = tx_buf;
        g_sci1_tx_count = tx_num;
        /* Set TXD1 pin */
        PORT1.PMR.BYTE |= 0x40U;
        SCI1.SCR.BIT.TIE = 1U;
        SCI1.SCR.BIT.TE = 1U;
    }

    return (status);
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
