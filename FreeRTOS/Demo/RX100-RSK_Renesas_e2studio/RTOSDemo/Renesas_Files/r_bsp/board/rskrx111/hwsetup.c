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
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name	   : hwsetup.c
* Device(s)    : RX
* H/W Platform : RSKRX210
* Description  : Defines the initialization routines used each time the MCU is restarted.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.11.2012 0.01     Beta Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* I/O Register and board definitions */
#include "platform.h"
/* Contains delcarations for the functions defined in this file */
#include "hwsetup.h"
#include "r_switches_config.h"
/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* MCU I/O port configuration function delcaration */
static void output_ports_configure(void);

/* Interrupt configuration function delcaration */
static void interrupts_configure(void);

/* MCU peripheral module configuration function declaration */
static void peripheral_modules_enable(void);


/***********************************************************************************************************************
* Function name: hardware_setup
* Description  : Contains setup functions called at device restart
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void hardware_setup(void)
{
    output_ports_configure();
    interrupts_configure();
    peripheral_modules_enable();
}

/***********************************************************************************************************************
* Function name: output_ports_configure
* Description  : Configures the port and pin direction settings, and sets the pin outputs to a safe level.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void output_ports_configure(void)
{
    /* Enable LEDs. */
    /* Start with LEDs off. */
    LED0 = LED_OFF;
    LED1 = LED_OFF;
    LED2 = LED_OFF;
    LED3 = LED_OFF;

    /* Set LED pins as outputs. */
    LED0_PDR = 1;
    LED1_PDR = 1;
    LED2_PDR = 1;
    LED3_PDR = 1;

    /* Enable switches. */
    /* Set pins as inputs. */
    SW1_PDR = 0;
    SW2_PDR = 0;
    SW3_PDR = 0;

    /* Set port mode registers for switches. */
    SW1_PMR = 0;
    SW2_PMR = 0;
    SW3_PMR = 0;

    /* Unlock MPC registers to enable writing to them. */
    MPC.PWPR.BIT.B0WI = 0 ;     /* Unlock protection register */
    MPC.PWPR.BIT.PFSWE = 1 ;    /* Unlock MPC registers */

    /* TXD1 is output. */
    PORT1.PDR.BIT.B6 = 1;
    PORT1.PMR.BIT.B6 = 1;
    MPC.P16PFS.BYTE  = 0x0A;
    /* RXD1 is input. */
    PORT1.PDR.BIT.B5 = 0;
    PORT1.PMR.BIT.B5 = 1;
    MPC.P15PFS.BYTE  = 0x0A;

    /* Configure the pin connected to the ADC Pot as an input */
    PORT4.PDR.BIT.B4 = 0;

    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA50B;

    /* Turn off module stop for the A2D converter. */
    SYSTEM.MSTPCRA.BIT.MSTPA17 = 0;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;

    /* Initialise the first button to generate an interrupt. */
    R_SWITCHES_Init();
}

/***********************************************************************************************************************
* Function name: interrupts_configure
* Description  : Configures interrupts used
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void interrupts_configure(void)
{
    /* Add code here to setup additional interrupts */
}

/***********************************************************************************************************************
* Function name: peripheral_modules_enable
* Description  : Enables and configures peripheral devices on the MCU
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void peripheral_modules_enable(void)
{
	/* Enable triggers to start an ADC conversion. */
	S12AD.ADCSR.BIT.TRGE = 1;

	/* Only channel 4 is going to be used. */
	S12AD.ADANSA.BIT.ANSA4 = 1;
}
