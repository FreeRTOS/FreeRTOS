/*Adapted for IAR Embedded Workbench*/
/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software.  By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2013, 2014 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_sci_user.c
* Version      : Code Generator for RX64M V1.00.01.01 [09 May 2014]
* Device(s)    : R5F571MLCxFC
* Tool-Chain   : IAR Embedded Workbench
* Description  : This file implements device driver for SCI module.
* Creation Date: 30/06/2014
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
#include "rskrx71mdef.h"
//_RB_#include "r_cg_cmt.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
extern uint8_t * gp_sci7_tx_address;                /* SCI7 send buffer address */
extern uint16_t  g_sci7_tx_count;                   /* SCI7 send data number */
extern uint8_t * gp_sci7_rx_address;                /* SCI7 receive buffer address */
extern uint16_t  g_sci7_rx_count;                   /* SCI7 receive data number */
extern uint16_t  g_sci7_rx_length;                  /* SCI7 receive data length */
/* Start user code for global. Do not edit comment generated here */

/* Global used to receive a character from the PC terminal */
uint8_t g_rx_char;

/* Flag used to control transmission to PC terminal */
volatile uint8_t g_tx_flag = FALSE;

/* Flag used locally to detect transmission complete */
static volatile uint8_t sci7_txdone;

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: r_sci7_transmit_interrupt
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#pragma vector=VECT(SCI7,TXI7)
__interrupt static void r_sci7_transmit_interrupt(void)
{
    if (g_sci7_tx_count > 0U)
    {
        SCI7.TDR = *gp_sci7_tx_address;
        gp_sci7_tx_address++;
        g_sci7_tx_count--;
    }
    else
    {
        SCI7.SCR.BIT.TIE = 0U;
        SCI7.SCR.BIT.TEIE = 1U;
    }
}

/***********************************************************************************************************************
* Function Name: r_sci7_transmitend_interrupt
* Description  : This function is TEI7 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci7_transmitend_interrupt(void)
{
    MPC.P90PFS.BYTE = 0x00U;
    PORT9.PMR.BYTE &= 0xFEU;
    SCI7.SCR.BIT.TIE = 0U;
    SCI7.SCR.BIT.TE = 0U;
    SCI7.SCR.BIT.TEIE = 0U;

    r_sci7_callback_transmitend();
}
/***********************************************************************************************************************
* Function Name: r_sci7_receive_interrupt
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
#pragma vector=VECT(SCI7,RXI7)
__interrupt static void r_sci7_receive_interrupt(void)
{
    if (g_sci7_rx_length > g_sci7_rx_count)
    {
        *gp_sci7_rx_address = SCI7.RDR;
        gp_sci7_rx_address++;
        g_sci7_rx_count++;

        if (g_sci7_rx_length <= g_sci7_rx_count)
        {
            r_sci7_callback_receiveend();
        }
    }
}
/***********************************************************************************************************************
* Function Name: r_sci7_receiveerror_interrupt
* Description  : This function is ERI7 interrupt service routine.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_sci7_receiveerror_interrupt(void)
{
    uint8_t err_type;

    r_sci7_callback_receiveerror();

    /* Clear overrun, framing and parity error flags */
    err_type = SCI7.SSR.BYTE;
    err_type &= 0xC7U;
    err_type |= 0xC0U;
    SCI7.SSR.BYTE = err_type;
}
/***********************************************************************************************************************
* Function Name: r_sci7_callback_transmitend
* Description  : This function is a callback function when SCI7 finishes transmission.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
static void r_sci7_callback_transmitend(void)
{
    /* Start user code. Do not edit comment generated here */
    sci7_txdone = TRUE;
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_sci7_callback_receiveend
* Description  : This function is a callback function when SCI7 finishes reception.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
static void r_sci7_callback_receiveend(void)
{
    /* Start user code. Do not edit comment generated here */
    /* Check the contents of g_rx_char */
    if ('z' == g_rx_char)
    {
        /* Stop the timer used to control transmission to PC terminal*/
//        R_CMT1_Stop();

        /* Turn off LED0 and turn on LED1 to indicate serial transmission
           inactive */
        LED0 = LED_OFF;
        LED1 = LED_ON;
    }
    else
    {
        /* Start the timer used to control transmission to PC terminal*/
//_RB_        R_CMT1_Start();

        /* Turn on LED0 and turn off LED1 to indicate serial transmission
           active */
        LED0 = LED_ON;
        LED1 = LED_OFF;
    }

    /* Set up SCI7 receive buffer again */
    R_SCI7_Serial_Receive((uint8_t *)&g_rx_char, 1);
   /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_sci7_callback_receiveerror
* Description  : This function is a callback function when SCI7 reception encounters error.
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
static void r_sci7_callback_receiveerror(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/***********************************************************************************************************************
* Function Name: R_SCI7_AsyncTransmit
* Description  : This function sends SCI7 data and waits for the transmit end flag.
* Arguments    : tx_buf -
*                    transfer buffer pointer
*                tx_num -
*                    buffer size
* Return Value : status -
*                    MD_OK or MD_ARGERROR
***********************************************************************************************************************/
MD_STATUS R_SCI7_AsyncTransmit (uint8_t * const tx_buf, const uint16_t tx_num)
{
    MD_STATUS status = MD_OK;

    /* clear the flag before initiating a new transmission */
    sci7_txdone = FALSE;

    /* Send the data using the API */
    status = R_SCI7_Serial_Send(tx_buf, tx_num);

    /* Wait for the transmit end flag */
    while (FALSE == sci7_txdone)
    {
        /* Wait */
    }
    return (status);
}
/***********************************************************************************************************************
* End of function R_SCI7_AsyncTransmit
***********************************************************************************************************************/


/* End user code. Do not edit comment generated here */
