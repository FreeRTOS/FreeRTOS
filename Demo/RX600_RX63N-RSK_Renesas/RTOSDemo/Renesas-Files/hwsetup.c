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
//#include "r_ether.h"
#include "rskrx63ndef.h"

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
//	SYSTEM.MSTPCRB.BIT.MSTPB15 = 0;				/* EtherC, EDMAC */
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
#if(0)
	/* ==== MII/RMII Pins setting ==== */
	/*--------------------------------------*/
	/*    Port Function Control Register    */
	/*--------------------------------------*/
#if ETH_MODE_SEL == ETH_MII_MODE
	/*	EE=1, PHYMODE=1, ENETE3=1, ENETE2=0, ENETE1=1, ENETE0=0 (Ethernet)	*/
	IOPORT.PFENET.BYTE = 0x9A;
#endif	/*	ETH_MODE_SEL	*/
#if ETH_MODE_SEL == ETH_RMII_MODE
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
#endif	/*	ETH_MODE_SEL	*/
#if ETH_MODE_SEL == ETH_RMII_MODE
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
#endif
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
unsigned long i;
    
    SYSTEM.PRCR.WORD = 0xA503;              /* Access registers via PRCR                    */

    SYSTEM.SOSCCR.BYTE = 0x00;              /* Sub-clock oscillator ON                      */
												
    SYSTEM.HOCOPCR.BYTE = 0x00;             /* HOCO ON                                      */
										
    SYSTEM.MOSCWTCR.BYTE = 0x0e;            /* Main Clock Oscillator Wait Control Register  */
                                            /* 262144 states                                */

    SYSTEM.PLLWTCR.BYTE = 0x0e;				/* PLL Wait Control Register                    */
                                            /* 2097152 states                               */
	
    SYSTEM.MOSCCR.BYTE = 0x00;				/* EXTAL ON                                     */

    SYSTEM.PLLCR2.BYTE = 0x01;				/* PLL OFF                                      */
    SYSTEM.PLLCR.WORD = 0x0f00;				/* x16 @PLL                                     */
                                            /* Input to PLL = EXTAL       	 	      */
                                            /* Therefore:                                   */
                                            /*   PLL = EXTAL                                */
                                            /*       = 12                                   */
                                            /*   PLL * 16 = 192MHz                          */	

                                            /* External oscillation input selection         */
	SYSTEM.PLLCR2.BYTE = 0x00;				/* PLL ON                                       */
	
	for(i = 0; i<2500; i++)                 /* Wait for stabilisation of PLL and main clock */
    {				                        /* = 20ms                                       */
                                            /*   (2500 x 1/125kHz = 20ms)                   */
                                               
	}
	
/************************************************************************/
/*                                                                      */
/*  SYSTEM.SCKCR.BIT.PCKB   = 2; ( b11: b8 ) PLL/4 = 48MHz		        */
/*  SYSTEM.SCKCR.BIT.PCKA   = 2; ( b15:b12 ) PLL/4 = 48MHz		        */  
/*  SYSTEM.SCKCR.BIT.BCK    = 2; ( b16:b19 ) PLL/4 = 48MHz		        */
/*  SYSTEM.SCKCR.BIT.PSTOP0 = 1; ( b22     ) SDCLK CLK OUT Disabled     */
/*  SYSTEM.SCKCR.BIT.PSTOP1 = 1; ( b23     ) BUS CLK OUT   Disabled     */
/*  SYSTEM.SCKCR.BIT.ICK    = 1; ( b24:b27 ) PLL/2 = 96MHz		        */
/*  SYSTEM.SCKCR.BIT.FCK    = 2; ( b31:b28 ) PLL/3 = 48MHz		        */
/*                                                                      */
/*  SYSTEM.SCKCR2.BIT.UCK   = 2;			 PLL/4 = 48MHz              */
/*  SYSTEM.SCKCR2.BIT.IEBCK = 3;			 PLL/4 = 48MHz		        */
/************************************************************************/
    
	SYSTEM.SCKCR.LONG = 0x21c22222;     /* set these bits to the same a this bit   */
/*                             |||               |                   |             */
/*                             |++---------------+                   |             */
/*					           |                                     |             */
/*                             +-------------------------------------+             */
	
    SYSTEM.SCKCR2.WORD = 0x0033;		


//	SYSTEM.SCKCR3.WORD = 0x0000;			/* LOCO -> LOCO         */
//	SYSTEM.SCKCR3.WORD = 0x0100;			/* LOCO -> HOCO         */
//	SYSTEM.SCKCR3.WORD = 0x0200;			/* LOCO -> MAIN         */
//	SYSTEM.SCKCR3.WORD = 0x0300;			/* LOCO -> Sub-Clock    */
	SYSTEM.SCKCR3.WORD = 0x0400;			/* LOCO -> PLL          */

#if 1
	// Configure LED - I/O pins as Outputs
	// First set the Data Levels
	LED0 = 1;	// LED0 : OFF =1, ON = 0
	LED1 = 1;	// LED1 : OFF =1, ON = 0
	LED2 = 1;	// LED2 : OFF =1, ON = 0
	LED3 = 1;	// LED3 : OFF =1, ON = 0

	// Set Port Direction Registers
	LED0_PDR = 1;	// LED0 : 1 = output
	LED1_PDR = 1;	// LED1 : 1 = output
	LED2_PDR = 1;	// LED2 : 1 = output
	LED3_PDR = 1;	// LED3 : 1 = output
#endif
	/* Gain access to the Port Function Select Registers */
	MPC.PWPR.BIT.B0WI = 0;
	MPC.PWPR.BIT.PFSWE = 1;
}

