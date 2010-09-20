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

/******************************************************************************
* Function Name: HardwareSetup
* Description  : This function does initial setting for CPG port pins used in
*			  : the Demo including the MII pins of the Ethernet PHY connection.
* Arguments	: none
* Return Value : none
******************************************************************************/
void HardwareSetup(void)
{

	unsigned long sckcr = 0;

	/* Configure system clocks based on header */
	sckcr += (ICLK_MUL==8) ? (0ul << 24) : (ICLK_MUL==4) ? (1ul << 24) : (ICLK_MUL==2) ? (2ul << 24) : (3ul << 24);
	sckcr += (BCLK_MUL==8) ? (0ul << 16) : (BCLK_MUL==4) ? (1ul << 16) : (BCLK_MUL==2) ? (2ul << 16) : (3ul << 16);
	sckcr += (PCLK_MUL==8) ? (0ul <<  8) : (PCLK_MUL==4) ? (1ul <<  8) : (PCLK_MUL==2) ? (2ul <<  8) : (3ul <<  8);
	SYSTEM.SCKCR.LONG = sckcr;

	/* Configure LED 0-5 pins as outputs */
	LED0 = LED_OFF; 
	LED1 = LED_OFF;
	LED2 = LED_OFF;
	LED3 = LED_OFF;
	LED4 = LED_OFF;
	LED5 = LED_OFF;
	LED0_DDR = 1; 
	LED1_DDR = 1;
	LED2_DDR = 1;
	LED3_DDR = 1;
	LED4_DDR = 1;
	LED5_DDR = 1;

	/* Configure SW 1-3 pins as inputs */
	SW1_DDR = 0;
	SW2_DDR = 0;
	SW3_DDR = 0;
	SW1_ICR = 1;
	SW2_ICR = 1;
	SW3_ICR = 1;

	
	/* Configure LCD pins as outputs - uncomment this if an LCD is present.
	LCD_RS_DDR = 1;
	LCD_EN_DDR = 1;
	LCD_DATA_DDR = 0xF0; */

	/* Initialize display - uncomment this if an LCD is present.
	InitialiseDisplay(); */
}

