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
*
****************************************************************************************************************************************************************/
/****************************************************************************************************************************************************************
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
****************************************************************************************************************************************************************/
/***********************************************************************************************************************
* File Name     : gnu_io.c
* Device(s)     : RZ/A1H RSK+T1
* Tool-Chain    : GNUARM-NONEv14.02-EABI
* H/W Platform  : RSK+T1 CPU Board
* Description   : Sample Program - GCC support for serial I/O
*               : Variants of this file can be created for each compiler
***********************************************************************************************************************/
/***********************************************************************************************************************
* History       : DD.MM.YYYY Version Description
*               : 21.05.2015 1.00
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Standard IO header */
#include <stdio.h>
/* Default  type definition header */
#include "r_typedefs.h"
/* Character I/O header */
#include "siochar.h"
/* I/O Register root header */
#include "iodefine.h"
/* Compiler specific UART i/O support header */
#include "gnu_io.h"


/***********************************************************************************************************************
* Function Name: put_string
* Description  : GNU interface to low-level I/O putchar replacement
* Arguments    : char * pString
* Return Value : none
***********************************************************************************************************************/
void put_string (char *pString)
{
    while(0 != (*pString))
    {
        io_put_char(*pString++);
    }
}

/***********************************************************************************************************************
 End of function put_string
***********************************************************************************************************************/

/***********************************************************************************************************************
* Function Name: get_string
* Description  : GNU interface to low-level I/O getchar replacement
* Arguments    : char * pString
* Return Value : none
***********************************************************************************************************************/
void get_string (char * pString)
{
    char * ptr = pString;

    do
    {
        (*ptr) = io_get_char();

        io_put_char(*ptr);

        if('\r' == (*ptr))
        {
            (*ptr) = 0;

            /* This is intentional since no more input is expected */
            break;
        }
    }
    while('\0' != (*ptr++));
    io_put_char('\r');
    io_put_char('\n');
}

/***********************************************************************************************************************
 End of function get_string
***********************************************************************************************************************/

