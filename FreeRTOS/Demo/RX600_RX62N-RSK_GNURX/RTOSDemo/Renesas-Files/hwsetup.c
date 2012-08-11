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
* File Name	: hwsetup.c
* Version	  : 1.00
* Description  : Power up hardware initializations
******************************************************************************
* History : DD.MM.YYYY Version Description
*		 : 15.02.2010 1.00	First Release
******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "iodefine.h"
#include "rskrx62ndef.h"
// #include "lcd.h" Uncomment this if an LCD is present.

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
	SYSTEM.MSTPCRB.BIT.MSTPB15 = 0;				/* EtherC, EDMAC */
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

	/* ==== MII/RMII Pins setting ==== */
	/*--------------------------------------*/
	/*    Port Function Control Register    */
	/*--------------------------------------*/
#if ETH_MODE_SEL == ETH_MII_MODE
	/*	EE=1, PHYMODE=1, ENETE3=1, ENETE2=0, ENETE1=1, ENETE0=0 (Ethernet)	*/
	IOPORT.PFENET.BYTE = 0x9A;
#else	/*	ETH_MODE_SEL	*/
	/*	EE=1, PHYMODE=0, ENETE3=0, ENETE2=0, ENETE1=1, ENETE0=0 (Ethernet)	*/
	IOPORT.PFENET.BYTE = 0x82;
#endif	/*	ETH_MODE_SEL	*/
	/*-------------------------------------------*/
	/*    Input Buffer Control Register (ICR)    */
	/*-------------------------------------------*/
#if ETH_MODE_SEL == ETH_MII_MODE
	/*	P54=1 Set ET_LINKSTA input	*/
	PORT5.ICR.BIT.B4 = 1;
	/*	P71=1 Set ET_MDIO input	*/
	PORT7.ICR.BIT.B1 = 1;
	/*	P74=1 Set ET_ERXD1 input	*/
	PORT7.ICR.BIT.B4 = 1;
	/*	P75=1 Set ET_ERXD0 input	*/
	PORT7.ICR.BIT.B5 = 1;
	/*	P76=1 Set ET_RX_CLK input	*/
	PORT7.ICR.BIT.B6 = 1;
	/*	P77=1 Set ET_RX_ER input	*/
	PORT7.ICR.BIT.B7 = 1;
	/*	P83=1 Set ET_CRS input	*/
	PORT8.ICR.BIT.B3 = 1;
	/*	PC0=1 Set ET_ERXD3 input	*/
	PORTC.ICR.BIT.B0 = 1;
	/*	PC1=1 Set ET_ERXD2 input	*/
	PORTC.ICR.BIT.B1 = 1;
	/*	PC2=1 Set ET_RX_DV input	*/
	PORTC.ICR.BIT.B2 = 1;
	/*	PC4=1 Set EX_TX_CLK input	*/
	PORTC.ICR.BIT.B4 = 1;
	/*	PC7=1 Set ET_COL input	*/
	PORTC.ICR.BIT.B7 = 1;
#else	/*	ETH_MODE_SEL	*/
	/*	P54=1 Set ET_LINKSTA input	*/
	PORT5.ICR.BIT.B4 = 1;
	/*	P71=1 Set ET_MDIO input	*/
	PORT7.ICR.BIT.B1 = 1;
	/* P74=1 Set RMII_RXD1 input	*/
	PORT7.ICR.BIT.B4 = 1;
	/* P75=1 Set RMII_RXD0 input	*/
	PORT7.ICR.BIT.B5 = 1;
	/* P76=1 Set REF50CLK input	*/
	PORT7.ICR.BIT.B6 = 1;
	/* P77=1 Set RMII_RX_ER input	*/
	PORT7.ICR.BIT.B7 = 1;
	/* P83=1 Set RMII_CRS_DV input	*/
	PORT8.ICR.BIT.B3 = 1;
#endif	/*	ETH_MODE_SEL	*/

    /* Configure LED 0-5 pin settings */
    PORT0.DR.BIT.B2 = 1; 
    PORT0.DR.BIT.B3 = 1;
    PORT0.DR.BIT.B5 = 1;
    PORT3.DR.BIT.B4 = 1;
    PORT6.DR.BIT.B0 = 1;
    PORT7.DR.BIT.B3 = 1;
    PORT0.DDR.BIT.B2 = 1; 
    PORT0.DDR.BIT.B3 = 1;
    PORT0.DDR.BIT.B5 = 1;
    PORT3.DDR.BIT.B4 = 1;
    PORT6.DDR.BIT.B0 = 1;
    PORT7.DDR.BIT.B3 = 1;

    /* Configure SW 1-3 pin settings */
    PORT0.DDR.BIT.B0 = 0;
    PORT0.DDR.BIT.B1 = 0;
    PORT0.DDR.BIT.B7 = 0;
    PORT0.ICR.BIT.B0 = 1;
    PORT0.ICR.BIT.B1 = 1;
    PORT0.ICR.BIT.B7 = 1;

#if INCLUDE_LCD == 1
    /* Set LCD pins as outputs */
    /* LCD-RS */
    PORT8.DDR.BIT.B4 = 1;
    /* LCD-EN */
    PORT8.DDR.BIT.B5 = 1;
    /*LCD-data */
    PORT9.DDR.BYTE = 0xF0;
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
	SYSTEM.SCKCR.LONG = 0x00020100;	/* Clockin = 12MHz */
									/* I Clock = 96MHz, B Clock = 24MHz, */
									/* P Clock = 48MHz */

}

