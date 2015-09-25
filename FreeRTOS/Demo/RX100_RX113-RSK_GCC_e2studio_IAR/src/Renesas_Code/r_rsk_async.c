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
 *******************************************************************************/
/* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.   */
/*******************************************************************************
 * File Name     : r_rsk_async.c
 * Version       : 1.00
 * Device(s)     : R5F51138AxFP
 * Tool-Chain    : CCRX
 * H/W Platform  : RSKRX113
 * Description   : Functions used to send data via the SCI in asynchronous mode
 *******************************************************************************/
/*******************************************************************************
 * History       : 26.08.2014  Ver. 1.00 First Release
 *******************************************************************************/

/*******************************************************************************
 System Includes
 *******************************************************************************/
/* Following header file provides string type definitions. */
#include <string.h>

/*******************************************************************************
 User Includes (Project Level Includes)
 *******************************************************************************/
/* Defines port registers */
#include "r_cg_macrodriver.h"
#include "r_cg_sci.h"
#include "r_rsk_async.h"

/*******************************************************************************
 User Defines
 *******************************************************************************/

/*******************************************************************************
 * Global Variables
 *******************************************************************************/

/* Declaration of the command string to clear the terminal screen */
static const char cmd_clr_scr[] =
{ 27, 91, 50, 74, 0, 27, 91, 72, 0 };

/*******************************************************************************
 * Function Prototypes
 *******************************************************************************/

/* text_write function prototype */
static void text_write (const char * const msg_string);

/*******************************************************************************
 * Function Name: R_ASYNC_Init
 * Description  : This function initialises the SCI channel connected to the
 *                RS232 connector on the RSK. The channel is configured for
 *                transmission and reception, and instructions are sent to the
 *                terminal.
 * Argument     : none
 * Return value : none
 *******************************************************************************/
void R_ASYNC_Init (void)
{

    /* Set up SCI1 receive buffer */
    R_SCI1_Serial_Receive((uint8_t *) &g_rx_char, 1);

    /* Enable SCI1 operations */
    R_SCI1_Start();

    /* Clear the text on terminal window */
    text_write(cmd_clr_scr);

    /* Display splash screen on terminal window */
    text_write("Renesas RSKRX113 Async Serial \r\n");

    /* Inform user on how to stop transmission */
    text_write("Press 'z' to stop and any key to resume\r\n\n");
}
/*******************************************************************************
 * End of function R_ASYNC_Init
 *******************************************************************************/

/*******************************************************************************
 * Function Name : text_write
 * Description   : Transmits null-terminated string.
 * Argument      : (char*) msg_string - null terminated string
 * Return value  : None
 *******************************************************************************/
static void text_write (const char * const msg_string)
{
    R_SCI1_AsyncTransmit((uint8_t *) msg_string, (uint16_t) strlen(msg_string));
}
/*******************************************************************************
 * End of function text_write
 *******************************************************************************/

