/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_hardware_setup.c
* Version      : 1.0.101
* Device(s)    : R5F572NNHxFB
* Description  : Initialization file for code generation configurations.
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_smc_cgc.h"
#include "r_smc_interrupt.h"
/* Start user code for include. Do not edit comment generated here */
#include "r_gpio_rx_if.h"
#include "r_sci_rx_pinset.h"
#include "r_sci_rx_if.h"
#include "r_dtc_rx_if.h"
#include "demo_specific_io.h"
/* End user code. Do not edit comment generated here */
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
/* Start user code for global. Do not edit comment generated here */

/* Board Support Data Structures. */
sci_hdl_t xSerialSciHandle;
dtc_transfer_data_t xSerialTxDtcInfo;

/* Workaround to execute FIT Board Support Settings */
void R_CG_Config_Create(void);
void R_FIT_Board_Support_Settings(void);
void R_Systeminit(void)
{
    R_CG_Config_Create();
    R_FIT_Board_Support_Settings();
}
#define R_Systeminit R_CG_Config_Create

/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
* Function Name: r_undefined_exception
* Description  : This function is undefined interrupt service routine
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/

void r_undefined_exception(void)
{
    /* Start user code for r_undefined_exception. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

/***********************************************************************************************************************
* Function Name: R_Systeminit
* Description  : This function initializes every configuration
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/

void R_Systeminit(void)
{
    /* Enable writing to registers related to operating modes, LPC, CGC and software reset */
    SYSTEM.PRCR.WORD = 0xA50BU;

    /* Enable writing to MPC pin function control registers */
    MPC.PWPR.BIT.B0WI = 0U;
    MPC.PWPR.BIT.PFSWE = 1U;

    /* Write 0 to the target bits in the POECR2 registers */
    POE3.POECR2.WORD = 0x0000U;

    /* Initialize clocks settings */
    R_CGC_Create();

    /* Register undefined interrupt */
    R_BSP_InterruptWrite(BSP_INT_SRC_UNDEFINED_INTERRUPT,(bsp_int_cb_t)r_undefined_exception);

    /* Disable writing to MPC pin function control registers */
    MPC.PWPR.BIT.PFSWE = 0U;
    MPC.PWPR.BIT.B0WI = 1U;

    /* Enable protection */
    SYSTEM.PRCR.WORD = 0xA500U;
}

/* Start user code for adding. Do not edit comment generated here */

void R_FIT_Board_Support_Settings(void)
{
    /* Do not call any functions which enables generating any interrupt requests. */

    /* GPIO for LED */
    R_GPIO_PinWrite(U_GPIO_PIN_LED0, (gpio_level_t)LED_OFF); // for the initial level after input --> output
    R_GPIO_PinDirectionSet(U_GPIO_PIN_LED0, GPIO_DIRECTION_OUTPUT);

    /* GPIO for SW */
    R_GPIO_PinDirectionSet(U_GPIO_PIN_SW1, GPIO_DIRECTION_INPUT );

    /* FreeRTOS CLI Command Console */
    U_SCI_UART_CLI_PINSET();
    sci_cfg_t xSerialSciConfig;
    xSerialSciConfig.async.baud_rate    = 115200;
    xSerialSciConfig.async.clk_src      = SCI_CLK_INT;
    xSerialSciConfig.async.data_size    = SCI_DATA_8BIT;
    xSerialSciConfig.async.parity_en    = SCI_PARITY_OFF;
    xSerialSciConfig.async.parity_type  = SCI_EVEN_PARITY;
    xSerialSciConfig.async.stop_bits    = SCI_STOPBITS_1;
    xSerialSciConfig.async.int_priority = 1; /* lowest at first. */
    R_SCI_Open(U_SCI_UART_CLI_SCI_CH, SCI_MODE_ASYNC, &xSerialSciConfig, vSerialSciCallback, &xSerialSciHandle);
    R_DTC_Open();
    R_DTC_Control(DTC_CMD_DTC_START, NULL, NULL);
}

/* End user code. Do not edit comment generated here */

