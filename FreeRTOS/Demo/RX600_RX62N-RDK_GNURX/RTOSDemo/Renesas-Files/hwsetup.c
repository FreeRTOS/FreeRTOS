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
#include "yrdkrx62ndef.h"
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

	/* Module standby clear - EtherC, EDMAC */
	SYSTEM.MSTPCRB.BIT.MSTPB15 = 0;

	PORT0.DDR.BYTE = 0x00 ;     // Port 0: inputs (IRQ's from ethernet & WiFi)
	PORT1.DDR.BYTE = 0x00 ;     // Port 1: inputs (IIC and USB settings will override these later)
	PORT2.DDR.BYTE = 0x1A ;     // Port 2: USB signals
	PORT3.DDR.BYTE = 0x04 ;     // Port 3: JTAG (P30, P31, P34), CAN (P32=Tx, P33=Rx), NMI (P35)
	PORT4.DDR.BYTE = 0x00 ;     // Port 4: Switches (P40-P42), AIN (P43-P47)
	PORT5.DDR.BYTE = 0x3B ;     // Port 5: Audio (P55,P54), BCLK (P53), SCI (P52=Rx, P50=Tx), LCD-RS (P51)

	PORTA.DR.BYTE = 0x00 ;      // Port A outputs all LOW to start
	PORTA.DDR.BYTE = 0xFF ;     // Port A: Expansion (PA0-PA2), Ether (PA3-PA5), Audio (PA6-PA7)

	PORTB.DR.BYTE = 0x00 ;
	PORTB.DDR.BYTE = 0x70 ;     // Port B: Ether

	PORTC.DR.BYTE = 0xF7 ;      // Port C: Chip selects, clock = high; IO reset = low (not reset, needed by Ether PHY)
	PORTC.DDR.BYTE = 0x7F ;     // Port C: SPI (PC0-2, PC4-7), IO reset (PC3)                

	// Ethernet settings
	IOPORT.PFENET.BYTE = 0x82;  // Enable Ether poins, RMII mode, enable LINKSTA
	PORTA.ICR.BIT.B5 = 1;       // ET_LINKSTA 
	PORTA.ICR.BIT.B3 = 1;       // ET_MDIO
	PORTB.ICR.BIT.B0 = 1;       // RMII_RXD1
	PORTB.ICR.BIT.B1 = 1;       // RMII_RXD0
	PORTB.ICR.BIT.B2 = 1;       // REF50CLK
	PORTB.ICR.BIT.B3 = 1;       // RMII_RX_ER
	PORTB.ICR.BIT.B7 = 1;       // RMII_CRS_DV


	/* Configure LEDs */
	LED4 = LED_OFF;
	LED5 = LED_OFF;
	LED6 = LED_OFF;
	LED7 = LED_OFF;
	LED8 = LED_OFF;
	LED9 = LED_OFF;
	LED10 = LED_OFF;
	LED11 = LED_OFF;
	LED12 = LED_OFF;
	LED13 = LED_OFF;
	LED14 = LED_OFF;
	LED15 = LED_OFF;

	LED4_DDR = 1;
	LED5_DDR = 1;
	LED6_DDR = 1;
	LED7_DDR = 1;
	LED8_DDR = 1;
	LED9_DDR = 1;
	LED10_DDR = 1;
	LED11_DDR = 1;
	LED12_DDR = 1;
	LED13_DDR = 1;
	LED14_DDR = 1;
	LED15_DDR = 1;

	/* Configure push button switches */
	SW1_DDR = 0;
	SW2_DDR = 0;
	SW3_DDR = 0;
	SW1_ICR = 1;
	SW2_ICR = 1;
	SW3_ICR = 1;
}


