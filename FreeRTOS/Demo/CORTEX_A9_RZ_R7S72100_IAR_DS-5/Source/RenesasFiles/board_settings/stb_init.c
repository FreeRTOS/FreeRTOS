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
* File Name    : stb_init.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.8
*              : ARM Complier
* OS           :
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Initialize peripheral function sample
* Operation    :
* Limitations  :
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "devdrv_common.h"       /* Common Driver Header */
#include "stb_init.h"
#include "iodefine.h"

/* Do not include the following pragmas when compiling with IAR. */
#ifndef __ICCARM__
	#pragma arm section code   = "CODE_RESET"
	#pragma arm section rodata = "CONST_RESET"
	#pragma arm section rwdata = "DATA_RESET"
	#pragma arm section zidata = "BSS_RESET"
#endif

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
* Function Name: StbInit
* Description  :
*              :
* Arguments    : none
* Return Value : none
******************************************************************************/
void STB_Init(void)
{
    volatile uint8_t dummy_buf;

    /* ---- The clock of all modules is permitted. ---- */
    CPG.STBCR2.BYTE  = 0x6Au;       /* Port level is keep in standby mode, [1], [1], [0],           */
                                    /* [1], [0], [1], CoreSight                                     */
    dummy_buf = CPG.STBCR2.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR3.BYTE  = 0x00u;       /* IEBus, IrDA, LIN0, LIN1, MTU2, RSCAN2, [0], PWM              */
    dummy_buf = CPG.STBCR3.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR4.BYTE  = 0x00u;       /* SCIF0, SCIF1, SCIF2, SCIF3, SCIF4, SCIF5, SCIF6, SCIF7       */
    dummy_buf = CPG.STBCR4.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR5.BYTE  = 0x00u;       /* SCIM0, SCIM1, SDG0, SDG1, SDG2, SDG3, OSTM0, OSTM1           */
    dummy_buf = CPG.STBCR5.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR6.BYTE  = 0x00u;       /* A/D, CEU, DISCOM0, DISCOM1, DRC0, DRC1, JCU, RTClock         */
    dummy_buf = CPG.STBCR6.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR7.BYTE  = 0x24u;       /* DVDEC0, DVDEC1, [1], ETHER, FLCTL, [1], USB0, USB1           */
    dummy_buf = CPG.STBCR7.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR8.BYTE  = 0x05u;       /* IMR-LS20, IMR-LS21, IMR-LSD, MMCIF, MOST50, [1], SCUX, [1]   */
    dummy_buf = CPG.STBCR8.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR9.BYTE  = 0x00u;       /* I2C0, I2C1, I2C2, I2C3, SPIBSC0, SPIBSC1, VDC50, VDC51       */
    dummy_buf = CPG.STBCR9.BYTE;    /* (Dummy read)                                                 */
    CPG.STBCR10.BYTE = 0x00u;       /* RSPI0, RSPI1, RSPI2, RSPI3, RSPI4, CD-ROMDEC, RSPDIF, RGPVG  */
    dummy_buf = CPG.STBCR10.BYTE;   /* (Dummy read)                                                 */
    CPG.STBCR11.BYTE = 0xC0u;       /* [1], [1], SSIF0, SSIF1, SSIF2, SSIF3, SSIF4, SSIF5           */
    dummy_buf = CPG.STBCR11.BYTE;   /* (Dummy read)                                                 */
    CPG.STBCR12.BYTE = 0xF0u;       /* [1], [1], [1], [1], SDHI00, SDHI01, SDHI10, SDHI11           */
    dummy_buf = CPG.STBCR12.BYTE;   /* (Dummy read)                                                 */
}


/* End of File */

