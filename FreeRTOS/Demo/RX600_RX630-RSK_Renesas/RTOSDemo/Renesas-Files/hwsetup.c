/******************************************************************************
* DISCLAIMER

* This software is supplied by Renesas Technology Corp. and is only 
* intended for use with Renesas products. No other uses are authorized.

* This software is owned by Renesas Technology Corp. and is protected under 
* all applicable laws, including copyright laws.

* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
* REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, 
* INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A 
* PARTICULAR PURPOSE AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY 
* DISCLAIMED.

* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
* TECHNOLOGY CORP. NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES 
* FOR ANY REASON RELATED TO THE THIS SOFTWARE, EVEN IF RENESAS OR ITS 
* AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.

* Renesas reserves the right, without notice, to make changes to this 
* software and to discontinue the availability of this software.  
* By using this software, you agree to the additional terms and 
* conditions found by accessing the following link:
* http://www.renesas.com/disclaimer
******************************************************************************
* Copyright (C) 2008. Renesas Technology Corp., All Rights Reserved.
*******************************************************************************	
* File Name    : hwsetup.c
* Version      : 1.00
* Description  : Power up hardware initializations
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 15.02.2010 1.00    First Release
******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include <stdint.h>
#include "iodefine.h"
#include "cgc.h"
#include "rskrx630def.h"

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
void io_set_cpg(void);
void ConfigurePortPins(void);
void EnablePeripheralModules(void);

/******************************************************************************
* Function Name: HardwareSetup
* Description  : This function does initial setting for CPG port pins used in
*              : the Demo including the MII pins of the Ethernet PHY connection.
* Arguments    : none
* Return Value : none
******************************************************************************/
void HardwareSetup(void)
{
	/* Gain access to the System control registers                           */
    /* Refer to section 13 of the Hardware User Manual for further details   */
    SYSTEM.PRCR.WORD = 0xA503;
    
    /* Gain access to the Port Function Select Registers                     */
	/* Refer to section 21 of the Hardware User Manual for further details   */
    MPC.PWPR.BIT.B0WI = 0;
	MPC.PWPR.BIT.PFSWE = 1;
    
    /* CPG setting */
    /* User defined values for XTAL, Clock Divders etc are set in cgc.h      */
    InitCGC();

	/* Setup the port pins */
	ConfigurePortPins();

    /* Enables peripherals */
    EnablePeripheralModules();

#if INCLUDE_LCD == 1
    /* Initialize display */
    InitialiseDisplay();
#endif
}

/******************************************************************************
* Function Name: EnablePeripheralModules
* Description  : Enables Peripheral Modules before use
* Arguments    : none
* Return Value : none
******************************************************************************/
void EnablePeripheralModules(void)
{
	/*  Module standby clear */
    SYSTEM.MSTPCRA.BIT.MSTPA15 = 0;             /* CMT0 */
}

/******************************************************************************
* Function Name: ConfigurePortPins
* Description  : Configures port pins.
* Arguments    : none
* Return Value : none
******************************************************************************/
void ConfigurePortPins(void)
{
/* Port pins default to inputs. To ensure safe initialisation set the pin states
before changing the data direction registers. This will avoid any unintentional
state changes on the external ports.
Many peripheral modules will override the setting of the port registers. Ensure
that the state is safe for external devices if the internal peripheral module is
disabled or powered down. */

    /* Set initial LED pin state to off */
    LED0     = 1; 
    LED1     = 1;
    LED2     = 1;
    LED3     = 1;
    /* Configure LED 0-3 pin settings */
    LED0_PDR = 1; 
    LED1_PDR = 1;
    LED2_PDR = 1;
    LED3_PDR = 1;

    /* Configure SW 1-3 pin settings */
    /* No need to configure inputs as they are inputs by default */

#if INCLUDE_LCD == 1
    /* Set LCD pins as outputs */
    /* LCD-RS */
    LCD_RS_PDR = 1;
    /* LCD-EN */
    LCD_EN = 1;
    /*LCD-data */
    LCD_DATA_PDR = 0xF0;
#endif
}
