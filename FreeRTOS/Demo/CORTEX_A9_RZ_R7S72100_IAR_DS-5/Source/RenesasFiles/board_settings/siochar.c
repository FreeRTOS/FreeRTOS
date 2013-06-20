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
* File Name    : siochar.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.8
*              : ARM Complier
* OS           : 
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Serial I/O character R/W (SCIF 2-ch process)
* Operation    : 
* Limitations  : 
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "dev_drv.h"                /* Device Driver common header */
#include "devdrv_scif_uart.h"       /* UART Driver header */
#include "sio_char.h"
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
* Function Name: IoInitScif2
* Description  : This function initializes SCIF channel 2 as UART mode.
*              : The transmit and the receive of SCIF channel 2 are enabled.
* Arguments    : none
* Return Value : none
******************************************************************************/
void IoInitScif2(void)
{
    /* P1=66.67MHz CKS=0 SCBRR=17 Bit rate error=0.46% => Baud rate=115200bps */
    R_SCIF_UART_Init(DEVDRV_CH_2, SCIF_UART_MODE_RW, 0, 17);

    /* === PORT ==== */
    /* ---- P3_0 : TxD2 ---- */
    PORT3.PMCn.BIT.PMCn0     = 1;
    PORT3.PFCAEn.BIT.PFCAEn0 = 1;
    PORT3.PFCEn.BIT.PFCEn0   = 0;
    PORT3.PFCn.BIT.PFCn0     = 1;
    PORT3.PIPCn.BIT.PIPCn0   = 1;

    /* ---- P3_2 : RxD2 ---- */
    PORT3.PMCn.BIT.PMCn2     = 1;
    PORT3.PFCAEn.BIT.PFCAEn2 = 0;
    PORT3.PFCEn.BIT.PFCEn2   = 1;
    PORT3.PFCn.BIT.PFCn2     = 1;
    PORT3.PIPCn.BIT.PIPCn2   = 1;

    /* ---- Serial control register (SCSCRi) setting ---- */
    SCIF2.SCSCR.WORD = 0x0030;
                            /* SCIF2 transmitting and receiving operations are enabled */
}

/******************************************************************************
* Function Name: IoGetchar
* Description  : One character is received from SCIF2, and it's data is returned.
*              : This function keeps waiting until it can obtain the receiving data.
* Arguments    : none
* Return Value : Character to receive (Byte).
******************************************************************************/
char_t IoGetchar(void)
{
    char_t data;

    /* Confirming receive error(ER,DR,BRK) */
    if (SCIF2.SCFSR.WORD & 0x09C)
    {
        /* Detect receive error */
        SCIF2.SCSCR.BIT.RE    = 0;      /* Disable reception             */
        SCIF2.SCFCR.BIT.RFRST = 1;      /* Reset receiving FIFO          */
        SCIF2.SCFCR.BIT.RFRST = 0;      /* Clearing FIFO reception reset */
        SCIF2.SCFSR.WORD     &= ~0x9C;  /* Error bit clear               */
        SCIF2.SCSCR.BIT.RE    = 1;      /* Enable reception              */
        return 0;
    }

    /* Is there receive FIFO data? */
    while (0 == SCIF2.SCFSR.BIT.RDF)
    {
        /* WAIT */
    }

    /* Read receive data */
    data = SCIF2.SCFRDR.BYTE;
    /* Clear RDF */
    SCIF2.SCFSR.BIT.RDF = 0;

    /* Is it overflowed? */
    if (1 == SCIF2.SCLSR.BIT.ORER)
    {
        SCIF2.SCLSR.BIT.ORER = 0;       /* ORER clear */
    }

    return data;
}

/******************************************************************************
* Function Name: IoPutchar
* Description  : Character "buffer" is output to SCIF2.
*              : This function keeps waiting until it becomes the transmission
*              : enabled state.
* Arguments    : char_t buffer : character to output
* Return Value : None
******************************************************************************/
void IoPutchar(char_t buffer)
{
    /* Check if it is possible to transmit (TDFE flag) */
    while (0 == SCIF2.SCFSR.BIT.TDFE)
    {
        /* Wait */
    }

    /* Write the receiving data in TDR */
    SCIF2.SCFTDR.BYTE = buffer;

    /* Clear TDRE and TEND flag */
    SCIF2.SCFSR.WORD &= ~0x0060;
}


/* End of File */

