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
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_bsp.h
* H/W Platform : GENERIC_RX72N
* Description  : Has the header files that should be included for this platform.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.10.2019 1.00     First Release
***********************************************************************************************************************/

/* Make sure that no other platforms have already been defined. Do not touch this! */
#ifdef  PLATFORM_DEFINED
#error  "Error - Multiple platforms defined in platform.h!"
#else
#define PLATFORM_DEFINED
#endif

#ifdef __cplusplus
extern "C" {
#endif

/***********************************************************************************************************************
INCLUDE APPROPRIATE MCU AND BOARD FILES
***********************************************************************************************************************/
#include    "mcu/all/r_bsp_common.h"
#include    "r_bsp_config.h"
#include    "mcu/all/r_rx_compiler.h"

#include    "r_bsp_interrupt_config.h"

#include    "mcu/all/lowlvl.h"
#include    "mcu/all/lowsrc.h"
#include    "mcu/all/r_bsp_mcu_startup.h"

#if defined(__CCRX__)
#include    "mcu/rx72n/register_access/ccrx/iodefine.h"
#elif defined(__GNUC__)
#include    "mcu/rx72n/register_access/gnuc/iodefine.h"
#elif defined(__ICCRX__)
#include    "mcu/rx72n/register_access/iccrx/iodefine.h"
#endif /* defined(__CCRX__), defined(__GNUC__), defined(__ICCRX__) */
#include    "mcu/rx72n/r_bsp_cpu.h"
#include    "mcu/rx72n/r_bsp_locking.h"
#include    "mcu/rx72n/mcu_clocks.h"
#include    "mcu/rx72n/mcu_info.h"
#include    "mcu/rx72n/mcu_init.h"
#include    "mcu/rx72n/mcu_interrupts.h"
#include    "mcu/rx72n/mcu_locks.h"
#include    "mcu/rx72n/mcu_mapped_interrupts_private.h"
#include    "mcu/rx72n/mcu_mapped_interrupts.h"
#include    "mcu/rx72n/vecttbl.h"

#include    "board/generic_rx72n/hwsetup.h"

#include    "mcu/all/r_bsp_interrupts.h"
#include    "mcu/all/r_bsp_software_interrupt.h"
#include    "mcu/all/r_rx_intrinsic_functions.h"
#include    "mcu/all/r_rtos.h"

#ifdef __cplusplus
}
#endif

#ifndef BSP_BOARD_GENERIC_RX72N
#define BSP_BOARD_GENERIC_RX72N

#endif /* BSP_BOARD_GENERIC_RX72N */

