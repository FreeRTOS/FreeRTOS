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
* File Name    : r_cg_scifa.c
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for SCIF module.
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
#include "r_cg_scifa.h"
/* Start user code for include. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
const uint8_t * gp_scifa2_tx_address;   /* SCIFA2 transmit buffer address */
uint16_t        g_scifa2_tx_count;      /* SCIFA2 transmit data number */
uint8_t *       gp_scifa2_rx_address;   /* SCIFA2 receive buffer address */
uint16_t        g_scifa2_rx_count;      /* SCIFA2 receive data number */
uint16_t        g_scifa2_rx_length;     /* SCIFA2 receive data length */
/* Start user code for global. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: R_SCIFA2_Create
* Description  : This function initializes SCIFA2.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCIFA2_Create(void)
{
    volatile uint16_t dummy;
    uint16_t w_count;

    /* Cancel SCIFA2 module stop state */
    MSTP(SCIFA2) = 0U;

    /* Disable TXIF2 interrupt */
    VIC.IEC3.LONG = 0x00008000UL;

    /* Disable RXIF2 interrupt */
    VIC.IEC3.LONG = 0x00004000UL;

    /* Disable BRIF2 interrupt */
    VIC.IEC3.LONG = 0x00002000UL;

    /* Disable DRIF2 interrupt */
    VIC.IEC3.LONG = 0x00010000UL;

    /* Clear transmit/receive enable bits */
    SCIFA2.SCR.BIT.TE = 0U;
    SCIFA2.SCR.BIT.RE = 0U;

    /* Reset transmit/receive FIFO data register operation */
    SCIFA2.FCR.BIT.TFRST = 1U;
    SCIFA2.FCR.BIT.RFRST = 1U;

    /* Read and clear status flags */
    dummy = SCIFA2.FSR.WORD;
    ( void ) dummy;
    SCIFA2.FSR.WORD = 0x00U;
    dummy = (uint16_t) SCIFA2.LSR.BIT.ORER;
    ( void ) dummy;
    SCIFA2.LSR.BIT.ORER = 0U;

    /* Set clock enable bits */
    SCIFA2.SCR.WORD = _SCIF_INTERNAL_SCK_UNUSED;

    /* Set transmission/reception format */
    SCIFA2.SMR.WORD = _SCIF_CLOCK_SERICLK_4 | _SCIF_STOP_1 | _SCIF_PARITY_DISABLE | _SCIF_DATA_LENGTH_8 | 
                      _SCIF_ASYNCHRONOUS_MODE;
    SCIFA2.SEMR.BYTE = _SCIF_16_BASE_CLOCK | _SCIF_NOISE_FILTER_ENABLE | _SCIF_DATA_TRANSFER_LSB_FIRST | 
                       _SCIF_BAUDRATE_SINGLE;

    /* Clear modulation duty register select */
    SCIFA2.SEMR.BIT.MDDRS = 0U;

    /* Set bit rate */
    SCIFA2.BRR_MDDR.BRR = 0x3CU;

    /* Wait for at least 1-bit interval */
    for (w_count = 0U; w_count < _SCIF_1BIT_INTERVAL_2; w_count++)
    {
        nop();
    }

    /* Set FIFO trigger conditions */
    SCIFA2.FTCR.WORD = _SCIF_TX_FIFO_TRIGGER_NUM_0 | _SCIF_TX_TRIGGER_TFTC_VALID | _SCIF_RX_FIFO_TRIGGER_NUM_1 | 
                       _SCIF_RX_TRIGGER_RFTC_VALID;
    SCIFA2.FCR.WORD = _SCIF_LOOPBACK_DISABLE | _SCIF_MODEM_CONTROL_DISABLE;

    /* Disable transmit/receive FIFO data register reset operation */
    SCIFA2.FCR.BIT.TFRST = 0U;
    SCIFA2.FCR.BIT.RFRST = 0U;

    /* Set TXIF2 interrupt priority */
    VIC.PRL111.LONG = _SCIF_PRIORITY_LEVEL2;

    /* Set TXIF2 interrupt address */
    VIC.VAD111.LONG = (uint32_t)r_scifa2_txif2_interrupt;

    /* Set RXIF2 interrupt priority */
    VIC.PRL110.LONG = _SCIF_PRIORITY_LEVEL3;

    /* Set RXIF2 interrupt address */
    VIC.VAD110.LONG = (uint32_t)r_scifa2_rxif2_interrupt;

    /* Set BRIF2 interrupt priority */
    VIC.PRL109.LONG = _SCIF_PRIORITY_LEVEL5;

    /* Set BRIF2 interrupt address */
    VIC.VAD109.LONG = (uint32_t)r_scifa2_brif2_interrupt;

    /* Set DRIF2 interrupt priority */
    VIC.PRL112.LONG = _SCIF_PRIORITY_LEVEL4;

    /* Set DRIF2 interrupt address */
    VIC.VAD112.LONG = (uint32_t)r_scifa2_drif2_interrupt;
}
/***********************************************************************************************************************
* Function Name: R_SCIFA2_Start
* Description  : This function starts SCIFA2.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCIFA2_Start(void)
{
    /* Enable TXIF2 interrupt */
    VIC.IEN3.LONG |= 0x00008000UL;

    /* Enable RXIF2 interrupt */
    VIC.IEN3.LONG |= 0x00004000UL;

    /* Enable BRIF2 interrupt */
    VIC.IEN3.LONG |= 0x00002000UL;

    /* Enable DRIF2 interrupt */
    VIC.IEN3.LONG |= 0x00010000UL;
}
/***********************************************************************************************************************
* Function Name: R_SCIFA2_Stop
* Description  : This function stops SCIFA2.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void R_SCIFA2_Stop(void)
{
    /* Disable serial transmit */
    SCIFA2.SCR.BIT.TE = 0U;

    /* Disable serial receive */
    SCIFA2.SCR.BIT.RE = 0U;

    /* Disable TXI interrupt */
    SCIFA2.SCR.BIT.TIE = 0U;

    /* Disable RXI and ERI interrupt */
    SCIFA2.SCR.BIT.RIE = 0U;

    /* Disable TXIF2 interrupt */
    VIC.IEC3.LONG = 0x00008000UL;

    /* Disable RXIF2 interrupt */
    VIC.IEC3.LONG = 0x00004000UL;

    /* Disable BRIF2 interrupt */
    VIC.IEC3.LONG = 0x00002000UL;

    /* Disable DRIF2 interrupt */
    VIC.IEC3.LONG = 0x00010000UL;
}
/***********************************************************************************************************************
* Function Name: R_SCIFA2_Serial_Receive
* Description  : This function receives SCIFA2 data.
* Arguments    : rx_buf -
*                    receive buffer pointer (Not used when receive data handled by DMAC)
*                rx_num -
*                    buffer size (Not used when receive data handled by DMAC)
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCIFA2_Serial_Receive(uint8_t * rx_buf, uint16_t rx_num)
{
    MD_STATUS status = MD_OK;

    if (rx_num < 1U)
    {
        status = MD_ARGERROR;
    }
    else
    {
        g_scifa2_rx_count = 0U;
        g_scifa2_rx_length = rx_num;
        gp_scifa2_rx_address = rx_buf;

        SCIFA2.FTCR.BIT.RFTC = _SCIF_RX_TRIG_NUM_2;

        SCIFA2.SCR.BIT.RE = 1U;
        SCIFA2.SCR.BIT.RIE = 1U;
        SCIFA2.SCR.BIT.REIE = 1U;
    }

    return (status);
}
/***********************************************************************************************************************
* Function Name: R_SCIFA2_Serial_Send
* Description  : This function transmits SCIFA2 data.
* Arguments    : tx_buf -
*                    transfer buffer pointer (Not used when transmit data handled by DMAC)
*                tx_num -
*                    buffer size (Not used when transmit data handled by DMAC)
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCIFA2_Serial_Send(const uint8_t * tx_buf, uint16_t tx_num)
{
    MD_STATUS status = MD_OK;

    if (tx_num < 1U)
    {
        status = MD_ARGERROR;
    }
    else
    {
        gp_scifa2_tx_address = tx_buf;
        g_scifa2_tx_count = tx_num;
        SCIFA2.SCR.BIT.TE = 1U;
        SCIFA2.SCR.BIT.TIE = 1U;
    }

    return (status);
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
