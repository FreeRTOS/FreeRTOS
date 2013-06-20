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
* File Name    : peripheral_init_basic.c
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
#include "devdrv_common.h"      /* Common Driver Header */
#include "iodefine.h"

/* Do not include the following pragmas when compiling with IAR. */
#ifndef __ICCARM__
	#pragma arm section code   = "CODE_BASIC_SETUP"
	#pragma arm section rodata = "CONST_BASIC_SETUP"
	#pragma arm section rwdata = "DATA_BASIC_SETUP"
	#pragma arm section zidata = "BSS_BASIC_SETUP"
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
void Peripheral_BasicInit(void);

/******************************************************************************
Private global variables and functions
******************************************************************************/
static void CPG_Init(void);
static void CS0_PORTInit(void);


/******************************************************************************
* Function Name: PeripheralBasicInit
* Description  :
*              :
*              :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Peripheral_BasicInit(void)
{
    /* ==== Clock Pulse Generator (CPG) setting ====*/
    CPG_Init();

    /* ==== Port setting ==== */
    CS0_PORTInit();

    /* ==== Bus State Controller (BSC) setting ==== */
    R_BSC_Init((uint8_t)(BSC_AREA_CS0 | BSC_AREA_CS1));
}

/******************************************************************************
* Function Name: CPG_Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
static void CPG_Init(void)
{
    volatile uint32_t dummy_buf_32b;
    volatile uint8_t  dummy_buf_8b;

    *(volatile uint32_t *)(0x3fffff80) = 0x00000001;
    dummy_buf_32b = *(volatile uint32_t *)(0x3fffff80);

    /* ==== CPG Settings ==== */
    CPG.FRQCR.WORD  = 0x1035u;      /* PLL(x30), I:G:B:P1:P0 = 30:20:10:5:5/2 */
    CPG.FRQCR2.WORD = 0x0001u;      /* CKIO:Output at time usually,           */
                                    /* Output when bus right is opened,       */
                                    /* output at standby"L"                   */
                                    /* Clockin = 13.33MHz, CKIO = 66.67MHz,   */
                                    /* I  Clock = 400.00MHz,                  */
                                    /* G  Clock = 266.67MHz,                  */
                                    /* B  Clock = 133.33MHz,                  */
                                    /* P1 Clock =  66.67MHz,                  */
                                    /* P0 Clock =  33.33MHz                   */

    /* ----  Writing to On-Chip Data-Retention RAM is enabled. ---- */
    CPG.SYSCR3.BYTE = 0x0Fu;
    dummy_buf_8b = CPG.SYSCR3.BYTE;
}

/******************************************************************************
* Function Name: CS0_PORTInit
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
static void CS0_PORTInit(void)
{
    /* ==== BSC settings ==== */

    /* ---- P9_1 : A25 ---- */
    PORT9.PMCn.BIT.PMCn1     = 1;
    PORT9.PFCAEn.BIT.PFCAEn1 = 0;
    PORT9.PFCEn.BIT.PFCEn1   = 0;
    PORT9.PFCn.BIT.PFCn1     = 0;
    PORT9.PIPCn.BIT.PIPCn1   = 1;

    /* ---- P9_0 : A24 ---- */
    PORT9.PMCn.BIT.PMCn0     = 1;
    PORT9.PFCAEn.BIT.PFCAEn0 = 0;
    PORT9.PFCEn.BIT.PFCEn0   = 0;
    PORT9.PFCn.BIT.PFCn0     = 0;
    PORT9.PIPCn.BIT.PIPCn0   = 1;

    /* ---- P8_15 : A23 ---- */
    PORT8.PMCn.BIT.PMCn15     = 1;
    PORT8.PFCAEn.BIT.PFCAEn15 = 0;
    PORT8.PFCEn.BIT.PFCEn15   = 0;
    PORT8.PFCn.BIT.PFCn15     = 0;
    PORT8.PIPCn.BIT.PIPCn15   = 1;

    /* ---- P8_14 : A22 ---- */
    PORT8.PMCn.BIT.PMCn14     = 1;
    PORT8.PFCAEn.BIT.PFCAEn14 = 0;
    PORT8.PFCEn.BIT.PFCEn14   = 0;
    PORT8.PFCn.BIT.PFCn14     = 0;
    PORT8.PIPCn.BIT.PIPCn14   = 1;

    /* ---- P8_13 : A21 ---- */
    PORT8.PMCn.BIT.PMCn13     = 1;
    PORT8.PFCAEn.BIT.PFCAEn13 = 0;
    PORT8.PFCEn.BIT.PFCEn13   = 0;
    PORT8.PFCn.BIT.PFCn13     = 0;
    PORT8.PIPCn.BIT.PIPCn13   = 1;

    /* ---- P7_6 : WE0# / DQMLL# ---- */
    PORT7.PMCn.BIT.PMCn6     = 1;
    PORT7.PFCAEn.BIT.PFCAEn6 = 0;
    PORT7.PFCEn.BIT.PFCEn6   = 0;
    PORT7.PFCn.BIT.PFCn6     = 0;
    PORT7.PIPCn.BIT.PIPCn6   = 1;

    /* ---- P7_8 : RD ---- */
    PORT7.PMCn.BIT.PMCn8     = 1;
    PORT7.PFCAEn.BIT.PFCAEn8 = 0;
    PORT7.PFCEn.BIT.PFCEn8   = 0;
    PORT7.PFCn.BIT.PFCn8     = 0;
    PORT7.PIPCn.BIT.PIPCn8   = 1;

    /* ---- P7_0 : CS0 ---- */
    PORT7.PMCn.BIT.PMCn0     = 1;
    PORT7.PFCAEn.BIT.PFCAEn0 = 0;
    PORT7.PFCEn.BIT.PFCEn0   = 0;
    PORT7.PFCn.BIT.PFCn0     = 0;
    PORT7.PIPCn.BIT.PIPCn0   = 1;

    /* ---- P3_7 : CS1 ---- */
    PORT3.PMCn.BIT.PMCn7     = 1;
    PORT3.PFCAEn.BIT.PFCAEn7 = 1;
    PORT3.PFCEn.BIT.PFCEn7   = 1;
    PORT3.PFCn.BIT.PFCn7     = 0;
    PORT3.PIPCn.BIT.PIPCn7   = 1;
}

/* End of File */

