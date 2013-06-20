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
* File Name    : resetprg.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.8
*              : ARM Complier
* OS           : 
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Sub Main
* Operation    : 
* Limitations  : 
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "devdrv_common.h"      /* Common Driver Header */
#include "devdrv_intc.h"        /* INTC Driver Header   */
#include "resetprg.h"
#include "sio_char.h"
#include "stb_init.h"
#include "port_init.h"

#pragma arm section code   = "CODE_RESET"
#pragma arm section rodata = "CONST_RESET"
#pragma arm section rwdata = "DATA_RESET"
#pragma arm section zidata = "BSS_RESET"

/******************************************************************************
Typedef definitions
******************************************************************************/


/******************************************************************************
Macro definitions
******************************************************************************/


/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/
extern void    VbarInit(void);
extern void    L1CacheInit(void);
extern int32_t $Super$$main(void);

/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/


/******************************************************************************
Private global variables and functions
******************************************************************************/


/*******************************************************************************
* Function Name: $Sub$$main
* Description  : 
* Arguments    : none
* Return Value : none
*******************************************************************************/
void $Sub$$main(void)
{
    STB_Init();

    /* ==== PORT setting ==== */
    PORT_Init();

    /* ==== BSC setting ==== */
    R_BSC_Init((uint8_t)(BSC_AREA_CS2 | BSC_AREA_CS3));

    /* ==== INTC setting ==== */
    R_INTC_Init();

    /* ==== Cache setting ==== */
//    io_init_cache();

    /* ==== Writeback Cache ==== */
//    io_cache_writeback();

    L1CacheInit();

    /* ==== Vector base address setting ==== */
    VbarInit();

    __enable_irq();
    __enable_fiq();

    /* ==== Function call of main function ==== */
    $Super$$main();
}


/* END of File */

