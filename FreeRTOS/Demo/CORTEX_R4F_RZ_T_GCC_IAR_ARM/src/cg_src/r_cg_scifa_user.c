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
* File Name    : r_cg_scifa_user.c
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
#include "r_typedefs.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
extern const uint8_t * gp_scifa2_tx_address;   /* SCIFA2 send buffer address */
extern uint16_t        g_scifa2_tx_count;      /* SCIFA2 send data number */
extern uint8_t *       gp_scifa2_rx_address;   /* SCIFA2 receive buffer address */
extern uint16_t        g_scifa2_rx_count;      /* SCIFA2 receive data number */
extern uint16_t        g_scifa2_rx_length;     /* SCIFA2 receive data length */
/* Start user code for global. Do not edit comment generated here */

/* Contains status of user input from the serial terminal program */
volatile uint8_t g_terminal_request = 0;

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: r_scifa2_txif2_interrupt
* Description  : This function is TXIF2 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_txif2_interrupt(void)
{
    uint16_t count = 0;

    /* Get the amount of untransmitted data stored in the FRDR register */
    uint16_t dummy_fdr = SCIFA2.FDR.BIT.T;

    /* Write data to the transmit FIFO data register */
    while ((g_scifa2_tx_count > 0U) && (count < _SCIF_FIFO_MAX_SIZE - dummy_fdr))
    {
        SCIFA2.FTDR = *gp_scifa2_tx_address;
        gp_scifa2_tx_address++;
        g_scifa2_tx_count--;
        count++;
    }

    if (SCIFA2.FSR.BIT.TDFE == 1U)
    {
        SCIFA2.FSR.BIT.TDFE = 0U;
    }

    if (g_scifa2_tx_count <= 0U)
    {
        SCIFA2.SCR.BIT.TIE = 0U;
        SCIFA2.SCR.BIT.TEIE = 1U;
    }

    /* Wait the interrupt signal is disabled */
    while (0U != (VIC.IRQS3.LONG & 0x00008000UL))
    {
        VIC.IEC3.LONG = 0x00008000UL;
    }

    VIC.IEN3.LONG |= 0x00008000UL;

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_scifa2_rxif2_interrupt
* Description  : This function is RXIF2 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_rxif2_interrupt(void)
{
    uint16_t count = 0;

    /* Get the amount of receive data stored in FRDR register */
    uint16_t dummy_fdr = SCIFA2.FDR.BIT.R;

    /* Read data from the receive FIFO data register */
    while ((g_scifa2_rx_length > g_scifa2_rx_count) && (count < dummy_fdr))
    {
        *gp_scifa2_rx_address = SCIFA2.FRDR;
        gp_scifa2_rx_address++;
        g_scifa2_rx_count++;
        count++;
    }

    /* If remaining data is less than the receive trigger number, receive interrupt will not occur.
       In this case, set trigger number to 1 to force receive interrupt for each one byte of data in FRDR */
    if ((g_scifa2_rx_length - g_scifa2_rx_count < _SCIF_RX_TRIG_NUM_2) && (SCIFA2.FTCR.BIT.RFTC != 1U))
    {
        SCIFA2.FTCR.BIT.RFTC = 1U;
    }

    /* Clear receive FIFO data full flag */
    if (SCIFA2.FSR.BIT.RDF == 1U)
    {
        SCIFA2.FSR.BIT.RDF = 0U;
    }

    if (g_scifa2_rx_length <= g_scifa2_rx_count)
    {
        /* All data received */
        SCIFA2.SCR.BIT.RE = 0U;
        r_scifa2_callback_receiveend();
    }

    /* Wait the interrupt signal is disabled */
    while (0U != (VIC.IRQS3.LONG & 0x00004000UL))
    {
        VIC.IEC3.LONG = 0x00004000UL;
    }

    VIC.IEN3.LONG |= 0x00004000UL;

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_scifa2_drif2_interrupt
* Description  : This function is TEIF 2 or DRIF2 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_drif2_interrupt(void)
{
    if (1U == SCIFA2.FSR.BIT.TEND)
    {
        SCIFA2.SPTR.BIT.SPB2DT = 0U;
        SCIFA2.SPTR.BIT.SPB2IO = 1U;
        SCIFA2.SCR.BIT.TE = 0U;
        SCIFA2.SCR.BIT.TEIE = 0U;
    }
    r_scifa2_callback_transmitend();

    /* Clear data ready detect flag */
    if (1U == SCIFA2.FSR.BIT.DR)
    {
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
        SCIFA2.FSR.BIT.DR = 0U;  
    }

    /* Wait the interrupt signal is disabled */
    while (0U != (VIC.IRQS3.LONG & 0x00010000UL))
    {
        VIC.IEC3.LONG = 0x00010000UL;
    }

    VIC.IEN3.LONG |= 0x00010000UL;

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_scifa2_brif2_interrupt
* Description  : This function is BRIF2 or ERIF2 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_brif2_interrupt(void)
{
    if (1U == SCIFA2.FSR.BIT.BRK)
    {
        r_scifa2_callback_error(BREAK_DETECT);
        /* Clear break detect flag */
        SCIFA2.FSR.BIT.BRK = 0U;
    }

    if (1U == SCIFA2.FSR.BIT.ER)
    {
        r_scifa2_callback_error(RECEIVE_ERROR);
        /* Clear receive error flag */
        SCIFA2.FSR.BIT.ER = 0U;
    }

    if (1U == SCIFA2.LSR.BIT.ORER)
    {
        r_scifa2_callback_error(OVERRUN_ERROR);
        /* Clear overrun error flag */
        SCIFA2.LSR.BIT.ORER = 0U;
    }

    /* Wait the interrupt signal is disabled */
    while (0U != (VIC.IRQS3.LONG & 0x00002000UL))
    {
        VIC.IEC3.LONG = 0x00002000UL;
    }

    VIC.IEN3.LONG |= 0x00002000UL;

    /* Dummy write */
    VIC.HVA0.LONG = 0x00000000UL;
}
/***********************************************************************************************************************
* Function Name: r_scifa2_callback_transmitend
* Description  : This function is a callback function when SCIFA2 finishes transmission.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_callback_transmitend(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_scifa2_callback_receiveend
* Description  : This function is a callback function when SCIFA2 finishes reception.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_callback_receiveend(void)
{
    /* Start user code. Do not edit comment generated here */

    /* Read the received data */
    uint8_t uart_in = SCIFA2.FRDR;

    /* Check if desired character is received */
    if (('c' != uart_in) || ('C' != uart_in))
    {
        /* Set global flag to indicate user requested ADC reading */
        g_terminal_request = 1U;
    }
    
    /* Re-enable receptions */
    SCIFA2.SCR.BIT.RE = 1U;        
    
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_scifa2_callback_error
* Description  : This function is a callback function when SCIFA2 reception encounters error.
* Arguments    : error_type -
*                    reception error type
* Return Value : None
***********************************************************************************************************************/
void r_scifa2_callback_error(scif_error_type_t error_type)
{
    /* Start user code. Do not edit comment generated here */

    /* Used to suppress the warning message generated for unused variables */
    UNUSED_PARAM(error_type);

    /* End user code. Do not edit comment generated here */
}

/* Start user code for adding. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
