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
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name    : scif_uart_userdef.c
* $Rev: $
* $Date::                           $
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.13
*              : ARM Complier
* OS           : 
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - SCIF UART device driver (User define function)
* Operation    : 
* Limitations  : 
*******************************************************************************/

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include <stdio.h>
#include "r_typedefs.h"
#include "dev_drv.h"                /* Device Driver common header */
#include "devdrv_scif_uart.h"       /* UART Driver header */
#include "devdrv_intc.h"            /* INTC Driver Header */
#include "iodefine.h"

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/

/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/

/******************************************************************************
Private global variables and functions
******************************************************************************/

/******************************************************************************
* Function Name: Userdef_SCIF2_UART_Init
* Description  :
* Arguments    : uint8_t  mode
*              : uint16_t cks
*              : uint8_t  scbrr
* Return Value : none
******************************************************************************/
void Userdef_SCIF2_UART_Init(uint8_t mode, uint16_t cks, uint8_t scbrr)
{
    /* ==== SCIF initial setting ==== */
    /* ---- Serial control register (SCSCR2) setting ---- */
    /* SCIF transmitting and receiving operations stop */
    SCIF2.SCSCR.WORD = 0x0000;

    if (SCIF_UART_MODE_W == (mode & SCIF_UART_MODE_W))
    {
        /* ---- FIFO control register (SCFCR2) setting ---- */
        SCIF2.SCFCR.BIT.TFRST = 1;  /* Transmit FIFO reset */
    }

    if (SCIF_UART_MODE_R == (mode & SCIF_UART_MODE_R))
    {
        /* ---- FIFO control register (SCFCR2) setting ---- */
        /* SCIF transmitting and receiving operations stop */
    	SCIF2.SCFCR.BIT.RFRST = 1;

    	/* Receive FIFO data register reset */
    }

    /* ---- Serial status register(SCFSR2) setting ---- */
    /* ER,BRK,DR bit clear */
    SCIF2.SCFSR.WORD &= 0xFF6E;

    /* ---- Line status register (SCLSR2) setting ---- */
    /* ORER bit clear */
    SCIF2.SCLSR.BIT.ORER  = 0;

    /* ---- Serial control register (SCSCR2) setting ---- */
    /* B'00 : Internal CLK */
    SCIF2.SCSCR.BIT.CKE   = 0x0;

    /* ---- Serial mode register (SCSMR2) setting ---- */
    /*  Communication mode 0: Asynchronous mode 			*/
    /*  Character length   0: 8-bit data					*/
    /*  Parity enable      0: Add and check are disabled	*/
    /*  Stop bit length    0: 1 stop bit					*/
    /*  Clock select       cks(argument) 					*/
    SCIF2.SCSMR.WORD = cks & 0x0003;

    /* ---- Sets the Serial extension mode register (SCEMR2) ---- */
    /* Baud rate generator double-speed mode, 0: Normal mode 	*/
    /* Base clock select in asynchronous mode, 					*/
    /*   0: Base clock is 16 times the bit rate 				*/
    SCIF2.SCEMR.WORD = 0x0000;

    /* ---- Bit rate register (SCBRR2) setting ---- */
    SCIF2.SCBRR.BYTE = scbrr;

    /* ---- FIFO control register (SCFCR2) setting ---- */
    /*  RTS output active trigger        :Initial value	*/
    /*  Receive FIFO data trigger        :1-data		*/
    /*  Transmit FIFO data trigger       :0-data		*/
    /*  Modem control enable             :Disabled		*/
    /*  Receive FIFO data register reset :Disabled		*/
    /*  Loop-back test                   :Disabled 		*/
    SCIF2.SCFCR.WORD = 0x0030;

    /* ---- Serial port register (SCSPTR2) setting ---- */
    /* Serial port  break output(SPB2IO)  1: Enabled */
    /* Serial port break data(SPB2DT)  1: High-level */
    SCIF2.SCSPTR.WORD |= 0x0003;
}

/* End of File */

