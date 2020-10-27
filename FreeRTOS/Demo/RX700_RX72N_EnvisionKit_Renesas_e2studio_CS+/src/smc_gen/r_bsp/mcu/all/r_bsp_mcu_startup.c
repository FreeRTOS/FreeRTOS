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
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_bsp_mcu_startup.c
* Description  : This module implements user startup specific functions.
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 28.02.2019 2.00     Merged processing of all devices.
*                               Fixed coding style.
*         : 26.07.2019 2.01     Modified comment of API function to Doxygen style.
*                               Added Initialization the trigonometric function unit in R_BSP_StartupOpen function.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Platform support. */
#include "platform.h"

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE != 0

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Error checking
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables (to be accessed by other files)
***********************************************************************************************************************/

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/

/**********************************************************************************************************************
 * Function Name: R_BSP_StartupOpen
 ******************************************************************************************************************//**
 * @brief Specifies settings to use the BSP and peripheral FIT modules. Call this function only when the BSP startup 
 * is disabled.
 * @details This function performs initialization for the interrupt callback, register protection, and the hardware 
 * and pins. These processing are needed for using the BSP and peripheral FIT modules. Thus, this function must be 
 * called in the beginning of the main function. Call this function only when the BSP startup is disabled.
 * @note The R_BSP_StartupOpen function performs a part of processing in the startup function.
 * See Section 5.18 in the application note for more information.
 */
void R_BSP_StartupOpen (void)
{
    /* Initializes the trigonometric function unit. */
#ifdef BSP_MCU_TRIGONOMETRIC
#ifdef __TFU
    R_BSP_INIT_TFU();
#endif
#endif
    /* Initialize RAM. */
    bsp_ram_initialize();

    /* Initialize MCU interrupt callbacks. */
    bsp_interrupt_open();

    /* Initialize register protection functionality. */
    bsp_register_protect_open();

    /* Configure the MCU and board hardware */
    hardware_setup();
} /* End of function R_BSP_StartupOpen() */

#endif /* BSP_CFG_STARTUP_DISABLE != 0 */

