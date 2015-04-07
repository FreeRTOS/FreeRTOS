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
* File Name    : bsc_userdef.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.8
*              : ARM Complier
* OS           :
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Common driver (User define function)
* Operation    :
* Limitations  :
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "dev_drv.h"            /* Device Driver common header */
#include "devdrv_common.h"      /* Common Driver Header */
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
/* The address when writing in a SDRAM mode register */
#define SDRAM_MODE_CS2    (*(volatile uint16_t *)(0x3FFFD040))
#define SDRAM_MODE_CS3    (*(volatile uint16_t *)(0x3FFFE040))

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
* Function Name: Userdef_BSC_CS0Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_BSC_CS0Init(void)
{
    /* ---- CS0BCR settings ---- */
    BSC.CS0BCR.LONG = 0x10000C00ul;
                                    /* Idle Cycles between Write-read Cycles    */
                                    /*  and Write-write Cycles : 1 idle cycle   */
                                    /* Data Bus Size: 16-bit                    */

    /* ---- CS0WCR settings ----  */
    BSC.CS0WCR.NORMAL.LONG = 0x00000B40ul;
                                    /* Number of Delay Cycles from Address,     */
                                    /*  CS0# Assertion to RD#,WEn Assertion     */
                                    /*  : 1.5 cycles                            */
                                    /* Number of Access Wait Cycles: 6 cycles   */
                                    /* Delay Cycles from RD,WEn# negation to    */
                                    /*  Address,CSn# negation: 0.5 cycles       */
}

/******************************************************************************
* Function Name: Userdef_BSC_CS1Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_BSC_CS1Init(void)
{
    /* ---- CS1BCR settings ---- */
    BSC.CS1BCR.LONG = 0x10000C00ul;
                                    /* Idle Cycles between Write-read Cycles    */
                                    /*  and Write-write Cycles : 1 idle cycle   */
                                    /* Data Bus Size: 16-bit                    */

    /* ---- CS1WCR settings ----  */
    BSC.CS1WCR.LONG = 0x00000B40ul;
                                    /* Number of Delay Cycles from Address,     */
                                    /*  CS0# Assertion to RD#,WEn Assertion     */
                                    /*  : 1.5 cycles                            */
                                    /* Number of Access Wait Cycles: 6 cycles   */
                                    /* Delay Cycles from RD,WEn# negation to    */
                                    /*  Address,CSn# negation: 0.5 cycles       */
}

/******************************************************************************
* Function Name: Userdef_BSC_CS2Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_BSC_CS2Init(void)
{
    /* ==== CS2BCR settings ==== */
    BSC.CS2BCR.LONG = 0x00004C00ul;
                                /* Idle Cycles between Write-read Cycles  */
                                /* and Write-write Cycles : 0 idle cycles */
                                /* Memory type :SDRAM                     */
                                /* Data Bus Size : 16-bit                 */

    /* ==== CS2WCR settings ==== */
    BSC.CS2WCR.SDRAM.LONG = 0x00000480ul;
                                /* CAS latency for Area 2 : 2 cycles */


    /* ==== Written in SDRAM Mode Register ==== */
    SDRAM_MODE_CS2 = 0;
                                /* The writing data is arbitrary            */
                                /* SDRAM mode register setting CS2 space    */
                                /* Burst read (burst length 1)./Burst write */
}

/******************************************************************************
* Function Name: Userdef_BSC_CS3Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_BSC_CS3Init(void)
{
    volatile int32_t cnt;

    cnt = 150;
    while (cnt-- > 0)
    {
        /* wait */
    }

    /* ==== CS3BCR settings ==== */
    BSC.CS3BCR.LONG = 0x00004C00ul;
                                /* Idle Cycles between Write-read Cycles  */
                                /* and Write-write Cycles : 0 idle cycles */
                                /* Memory type :SDRAM                     */
                                /* Data Bus Size : 16-bit                 */

    /* ==== CS3WCR settings ==== */
    BSC.CS3WCR.SDRAM.LONG = 0x00002492ul;
                                /* Precharge completion wait cycles: 1 cycle     */
                                /* Wait cycles between ACTV command              */
                                /* and READ(A)/WRITE(A) command : 1 cycles       */
                                /* CAS latency for Area 3 : 2 cycles             */
                                /* Auto-precharge startup wait cycles : 2 cycles */
                                /* Idle cycles from REF command/self-refresh     */
                                /* Release to ACTV/REF/MRS command : 5 cycles    */

    /* ==== SDCR settings ==== */
    BSC.SDCR.LONG = 0x00120812ul;
                                /* Row address for Area 2 : 13-bit    */
                                /* Column Address for Area 2 : 10-bit */
                                /* Refresh Control :Refresh           */
                                /* RMODE :Auto-refresh is performed   */
                                /* BACTV :Auto-precharge mode         */
                                /* Row address for Area 3 : 13-bit    */
                                /* Column Address for Area 3 : 10-bit */

    /* ==== RTCOR settings ==== */
    BSC.RTCOR.LONG = 0xA55A0020ul;
                                /* 7.813usec /240nsec            */
                                /*   = 32(0x20)cycles per refresh */

    /* ==== RTCSR settings ==== */
    BSC.RTCSR.LONG = 0xA55A0010ul;
                                /* Initialization sequence start */
                                /* Clock select B-phy/16         */
                                /* Refresh count :Once           */

    /* ==== Written in SDRAM Mode Register ==== */
    SDRAM_MODE_CS3 = 0;
                                /* The writing data is arbitrary            */
                                /* SDRAM mode register setting CS3 space    */
                                /* Burst read (burst length 1)./Burst write */
}

/******************************************************************************
* Function Name: Userdef_BSC_CS4Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_BSC_CS4Init(void)
{
}

/******************************************************************************
* Function Name: Userdef_BSC_CS5Init
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_BSC_CS5Init(void)
{
}


/* End of File */

