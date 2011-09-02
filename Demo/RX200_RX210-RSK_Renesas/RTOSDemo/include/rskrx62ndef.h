
/******************************************************************************
* DISCLAIMER
* Please refer to http://www.renesas.com/disclaimer
******************************************************************************
  Copyright (C) 2008. Renesas Technology Corp., All Rights Reserved.
*******************************************************************************
* File Name    : rsksh7216.h
* Version      : 1.00
* Description  : RSK 7216 board specific settings
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 06.10.2009 1.00    First Release
******************************************************************************/

#ifndef RSKRX62N_H
#define RSKRX62N_H

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/

/* System Clock Settings */

/* DETAIL THIS LATER !!!! */

#define     XTAL_FREQUENCY  (50000000L)	
#define     ICLK_MUL        (1)
#define     PCLK_MUL        (2)
#define     BCLK_MUL        (2)
#define     ICLK_FREQUENCY  (XTAL_FREQUENCY * ICLK_MUL)
#define     PCLK_FREQUENCY  (XTAL_FREQUENCY / PCLK_MUL)
#define     BCLK_FREQUENCY  (XTAL_FREQUENCY / BCLK_MUL)

#define     CMT0_CLK_SELECT (512)

/* General Values */
#define		LED_ON          (0)
#define 	LED_OFF			(1)
#define 	SET_BIT_HIGH	(1)
#define 	SET_BIT_LOW		(0)
#define 	SET_BYTE_HIGH	(0xFF)
#define 	SET_BYTE_LOW	(0x00)

/* Define switches to be polled if not available as interrupts */
#define		SW_ACTIVE		FALSE
#define 	SW1 			PORT0.DR.BIT.B0
#define 	SW2 			PORT0.DR.BIT.B1
#define     SW3             PORT0.DR.BIT.B7
#define 	SW1_DDR			PORT0.DDR.BIT.B0
#define 	SW2_DDR			PORT0.DDR.BIT.B1
#define     SW3_DDR         PORT0.DDR.BIT.B7
#define 	SW1_ICR			PORT0.ICR.BIT.B0
#define 	SW2_ICR			PORT0.ICR.BIT.B1
#define     SW3_ICR         PORT0.ICR.BIT.B7

/* LEDs */
#define		LED0			PORT1.PODR.BIT.B4
#define		LED1			PORT1.PODR.BIT.B5
#define		LED2			PORT1.PODR.BIT.B6
#define		LED3			PORT1.PODR.BIT.B7
//#define	    LED4			PORT6.DR.BIT.B0
//#define	    LED5			PORT7.DR.BIT.B3
#define		LED0_DDR        PORT1.PDR.BIT.B4
#define		LED1_DDR        PORT1.PDR.BIT.B5
#define		LED2_DDR        PORT1.PDR.BIT.B6
#define		LED3_DDR        PORT1.PDR.BIT.B7
//#define	    LED4_DDR        PORT6.DDR.BIT.B0
//#define	    LED5_DDR        PORT7.DDR.BIT.B3

/* 2x8 segment LCD */
#define		INCLUDE_LCD		1
#define     LCD_RS          PORTJ.PODR.BIT.B1
#define     LCD_EN          PORTJ.PODR.BIT.B3
#define     LCD_DATA        PORTH.PODR.BYTE

#define     LCD_RS_DDR      PORTJ.PDR.BIT.B1
#define     LCD_EN_DDR      PORTJ.PDR.BIT.B3
#define     LCD_DATA_DDR    PORTH.PDR.BYTE



/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/



/* RSKRX62N_H */
#endif		

