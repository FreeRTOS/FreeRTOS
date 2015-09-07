/***********************************************************************************************************************
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
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* System Name  : RZ/T1 SCIF program
* File Name    : siochar.c
* Version      : 0.1
* Device       : R7S910018
* Abstract     : Serial I/O settings controlling the character
* Tool-Chain   : GNUARM-NONEv14.02-EABI
* OS           : not use
* H/W Platform : Renesas Starter Kit for RZ/T1(Preliminary)
* Description  : Control the character with serial I/O  
* Limitation   : none
***********************************************************************************************************************/
/***********************************************************************************************************************
* History      : DD.MM.YYYY Version  Description
*              : 21.05.2015 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_userdefine.h" 
#include "r_cg_scifa.h"
#include "siochar.h"


/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/


/***********************************************************************************************************************
Imported global variables and functions (from other files)
***********************************************************************************************************************/


/***********************************************************************************************************************
Exported global variables and functions (to be accessed by other files)
***********************************************************************************************************************/


/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/


/***********************************************************************************************************************
* Function Name: io_init_scifa2
* Description  : This function initialises SCIFA channel 2 as UART mode.
*              : The transmit and the receive of SCIFA channel 2 are enabled.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
void io_init_scifa2 (void)
{
    /* === Initialisation of SCIFA2 if not already initialised ==== */
    if (1 == MSTP_SCIFA2)
    {
        R_SCIFA2_Create();
    }
    
    /* Ensure receive FIFO trigger is set to 1 */ 
    SCIFA2.FCR.BIT.RTRG = 0U;
        
    /* Reception triggered by one data */
    SCIFA2.FTCR.BIT.RFTC = 1u;

    /* Enable reception and receive interrupts */
    SCIFA2.SCR.BIT.RE = 1U;
    SCIFA2.SCR.BIT.RIE = 1U;
    SCIFA2.SCR.BIT.REIE = 1U;
}

/***********************************************************************************************************************
 End of function io_init_scifa2
***********************************************************************************************************************/


/***********************************************************************************************************************
 * Function Name: io_get_char
* Description  : One character is received from SCIFA2, and it's data is returned.
*              : This function keeps waiting until it can obtain the receiving data.
* Arguments    : none
* Return Value : Character to receive (Byte).
***********************************************************************************************************************/
char io_get_char (void)
{
    char    data;
    
    /* Confirming receive error (ER,BRK,FER,PER) */
    if (SCIFA2.FSR.WORD & 0x09Cu)
    {
        /* ---- Detect receive error ---- */
        
        /* Disable reception */
        SCIFA2.SCR.BIT.RE = 0U;
        
        /* Reset receiving FIFO */
        SCIFA2.FCR.BIT.RFRST = 1U;
        
        /* Clearing FIFO reception reset */
        SCIFA2.FCR.BIT.RFRST = 0U;
        
        /* Error bit clear */ 
        SCIFA2.FSR.BIT.DR  = 0U;
        SCIFA2.FSR.BIT.RDF = 0U;
        
        /* Enable reception */
        SCIFA2.SCR.BIT.RE = 1U;

        return (0);
    }

    /* Is there receive FIFO data? */
    while (0 == SCIFA2.FSR.BIT.RDF)
    {
        /* Wait */
    }

    /* Read receive data */
    data = SCIFA2.FRDR;

    /* Clear RDF */
    SCIFA2.FSR.BIT.RDF = 0U;

    /* Is it overflowed? */
    if (1 == SCIFA2.LSR.BIT.ORER)
    {
        /* ORER clear */
        SCIFA2.LSR.BIT.ORER = 0U;
    }

    return (data);
}

/***********************************************************************************************************************
 End of function io_get_char
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name: io_put_char
* Description  : Character "buffer" is output to SCIFA2.
*              : This function keeps waiting until it becomes the transmission
*              : enabled state.
* Arguments    : char buffer : character to output
* Return Value : None
***********************************************************************************************************************/
void io_put_char (char buffer)
{     
    /* Check if it is possible to transmit (TDFE flag) */
    while (0 == SCIFA2.FSR.BIT.TDFE)
    {
        /* Wait */
    }

    /* Send the character via the terminal output */
    R_SCIFA2_Serial_Send((uint8_t *)&buffer, 1); 

    /* Clear TEND flag */
    SCIFA2.FSR.BIT.TEND = 0u;
}

/***********************************************************************************************************************
* End of function io_put_char
***********************************************************************************************************************/


/* End of File */

