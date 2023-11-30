/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2011 Renesas Electronics Corporation. All rights reserved.    
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : mcu_info.h
* Device(s)    : RX111
* Description  : Information about the MCU on this board (RSKRX111).
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.11.2012 0.01     Beta Release
***********************************************************************************************************************/

#ifndef _MCU_INFO
#define _MCU_INFO

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Gets MCU configuration information. */
#include "r_bsp_config.h"

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
/* MCU Series. */
#if   MCU_PART_SERIES == 0x0
    #define MCU_SERIES_RX100    (1)
#else
    #error "ERROR - MCU_PART_SERIES - Unknown MCU Series chosen in r_bsp_config.h"
#endif

/* MCU Group name. */
#if   MCU_PART_GROUP == 0x1
    #define MCU_RX111           (1)
    #define MCU_RX11x           (1)
#else
    #error "ERROR - MCU_PART_GROUP - Unknown MCU Group chosen in r_bsp_config.h"
#endif

/* Package. */
#if   MCU_PART_PACKAGE == 0x0
    #define PACKAGE_LFQFP64     (1)
#elif MCU_PART_PACKAGE == 0x1
    #define PACKAGE_LQFP64      (1)
#elif MCU_PART_PACKAGE == 0x2
    #define PACKAGE_TFLGA64     (1)
#elif MCU_PART_PACKAGE == 0x3
    #define PACKAGE_LFQFP48     (1)
#elif MCU_PART_PACKAGE == 0x4
    #define PACKAGE_VQFN48      (1)
#elif MCU_PART_PACKAGE == 0x5
    #define PACKAGE_HWQFN36     (1)
#elif MCU_PART_PACKAGE == 0x6
    #define PACKAGE_WFLGA36     (1)
#elif MCU_PART_PACKAGE == 0x7
    #define PACKAGE_SSOP36      (1)
#else
    #error "ERROR - MCU_PART_PACKAGE - Unknown package chosen in r_bsp_config.h"
#endif

/* Memory size of your MCU. */
#if   MCU_PART_MEMORY_SIZE == 0x0			// "J" parts
    #define ROM_SIZE_BYTES      (16384)
    #define RAM_SIZE_BYTES      (8192)
    #define DF_SIZE_BYTES       (8192)
#elif MCU_PART_MEMORY_SIZE == 0x1
    #define ROM_SIZE_BYTES      (32768)
    #define RAM_SIZE_BYTES      (10240)
    #define DF_SIZE_BYTES       (8192)
#elif MCU_PART_MEMORY_SIZE == 0x3
    #define ROM_SIZE_BYTES      (65536)
    #define RAM_SIZE_BYTES      (10240)
    #define DF_SIZE_BYTES       (8192)
#elif MCU_PART_MEMORY_SIZE == 0x4
    #define ROM_SIZE_BYTES      (98304)
    #define RAM_SIZE_BYTES      (16384)
    #define DF_SIZE_BYTES       (8192)
#elif MCU_PART_MEMORY_SIZE == 0x5
    #define ROM_SIZE_BYTES      (131072)
    #define RAM_SIZE_BYTES      (16384)
    #define DF_SIZE_BYTES       (8192)
#else
    #error "ERROR - MCU_PART_MEMORY_SIZE - Unknown memory size chosen in r_bsp_config.h"
#endif

/* System clock speed in Hz. */
#define ICLK_HZ             (((XTAL_HZ/PLL_DIV) * PLL_MUL) / ICK_DIV)
/* Peripheral Module Clock B speed in Hz. */
#define PCLKB_HZ            (((XTAL_HZ/PLL_DIV) * PLL_MUL) / PCKB_DIV)
/* Peripheral Module Clock D speed in Hz. */
#define PCLKD_HZ            (((XTAL_HZ/PLL_DIV) * PLL_MUL) / PCKD_DIV)
/* FlashIF clock speed in Hz. */
#define FCLK_HZ             (((XTAL_HZ/PLL_DIV) * PLL_MUL) / FCK_DIV)

#endif /* _MCU_INFO */

