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
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
************************************************************************************************************************/
/***********************************************************************************************************************
* File Name     : compiler_settings.h
* Device(s)     : RZ/A1H (R7S910018)
* Tool-Chain    : GNUARM-NONEv14.02-EABI
* H/W Platform  : RSK+T1 CPU Board
* Description   : Any compiler specific settings are stored here.
*               : Variants of this file must be created for each compiler
***********************************************************************************************************************/
/***********************************************************************************************************************
* History       : DD.MM.YYYY Version Description
*               : 21.05.2015 1.00
***********************************************************************************************************************/


/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Compiler specific UART i/O support header */
#include "../../GCC/inc/gnu_io.h"

#ifndef COMPILER_SETTINGS_H
#define COMPILER_SETTINGS_H

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* Definitions of SDRAM sections from the linker */
#define BSS_SDRAM0_SECTION __attribute__ ((section (".sdram0_section")))
#define BSS_SDRAM1_SECTION __attribute__ ((section (".sdram1_section")))

/***********************************************************************************************************************
Variable External definitions and Function External definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Functions Prototypes
***********************************************************************************************************************/

/* COMPILER_SETTINGS_H */
#endif  

/* End of File */
