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
#include "rskrx210def.h"
#include "hd44780.h"  /* EZ-LCD include file */

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
	/* CPG setting */
	io_set_cpg();

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
    /* Configure LED 0-4 pin settings */
    PORT1.PODR.BIT.B4 = 1; 
    PORT1.PODR.BIT.B5 = 1;
    PORT1.PODR.BIT.B6 = 1;
    PORT1.PODR.BIT.B7 = 1;

    PORT1.PDR.BIT.B4 = 1; 
    PORT1.PDR.BIT.B5 = 1;
    PORT1.PDR.BIT.B6 = 1;
    PORT1.PDR.BIT.B7 = 1;

   


#if INCLUDE_LCD == 1
    /* Set LCD pins as outputs */
    /* LCD-RS */
    PORTJ.PDR.BIT.B1 = 1;
    /* LCD-EN */
    PORTJ.PDR.BIT.B3 = 1;
    /*LCD-data */
    PORTH.PDR.BYTE = 0x0F;
#endif
}

/******************************************************************************
* Function Name: io_set_cpg
* Description  : Sets up operating speed
* Arguments    : none
* Return Value : none
******************************************************************************/
void io_set_cpg(void)
{
/* Set CPU PLL operating frequencies. Changes to the peripheral clock will require
changes to the debugger and flash kernel BRR settings. */

	/* ==== CPG setting ==== */

	unsigned int i;

	SYSTEM.PRCR.WORD = 0xA503;				/* Protect off 						*/

#if (CLK_SRC_HOCO == 1)	
	SYSTEM.HOCOPCR.BYTE = 0x00;				/* HOCO power supply on */
	SYSTEM.HOCOCR2.BYTE = 0x03;				/* Select - 50MHz */
	SYSTEM.HOCOCR.BYTE  = 0x01;				/* HOCO is operating */

	for(i=0; i<10; i++){					/* wait over 60us */
	}
#else
	SYSTEM.MOSCWTCR.BYTE = 0x0C;			/* Main Clock Oscillator Wait Control Register */
											/* 65536 states 					*/
											/* wait over 2 ms  @20MHz 			*/

	SYSTEM.PLLWTCR.BYTE = 0x0B;				/* PLL Wait Control Register 		*/
											/* 262144 states 					*/
											/* wait over 2.1 ms  @PLL = 80Hz	*/
											/*					(20/2x8*8) 		*/
	
	SYSTEM.PLLCR.WORD = 0x0701;				/* x8 @PLL 							*/
											/* Input to PLL (EXTAL in) / 2 		*/
											/* Therefore: 
													PLL = EXTAL / 2 	
														= 20M / 2
														= 10MHz														
												PLL * 8 = 80Mhz					*/	
	
	SYSTEM.MOSCCR.BYTE = 0x02;				/* EXTAL ON */
											/* External oscillation input selection */
	SYSTEM.PLLCR2.BYTE = 0x00;				/* PLL ON */
	
	for(i = 0; i<263; i++){					/* wait over 2.1ms */
	}
#endif
	
//	SYSTEM.SCKCR.LONG = 0x21823333;			/* ICK=PLL/2,FCK,PCK,BCL=PLL/4 */
/************************************************************************/
/*  If setting bits individually, rather than a single long write, 		*/
/*	set the BCK value before that of ICK 								*/
/************************************************************************/
	SYSTEM.SCKCR.BIT.PCKD 	= 3;			/* PLL/8 = 10MHz		*/
	SYSTEM.SCKCR.BIT.PCKC 	= 3;			/* PLL/8 = 10MHz		*/	
	SYSTEM.SCKCR.BIT.PCKB 	= 3;			/* PLL/8 = 10MHz		*/
	SYSTEM.SCKCR.BIT.PCKA 	= 3;			/* PLL/8 = 10MHz		*/
	SYSTEM.SCKCR.BIT.BCK 	= 3;			/* PLL/8 = 10MHz		*/
	SYSTEM.SCKCR.BIT.PSTOP1 = 1;			/* BUS CLK OUT Disabled */
	SYSTEM.SCKCR.BIT.ICK 	= 1;			/* PLL/2 = 40MHz		*/
	SYSTEM.SCKCR.BIT.FCK 	= 2;			/* PLL/4 = 20MHz		*/

	while(SYSTEM.OPCCR.BIT.OPCMTSF == 1);
	SYSTEM.OPCCR.BIT.OLPCM = 0;
	while(SYSTEM.OPCCR.BIT.OPCMTSF == 1);
#if (CLK_SRC_HOCO == 1)	
	SYSTEM.SCKCR3.WORD = 0x0100;			/* LOCO -> HOCO */
#else
	SYSTEM.SCKCR3.WORD = 0x0400;			/* LOCO -> PLL */
#endif
}
