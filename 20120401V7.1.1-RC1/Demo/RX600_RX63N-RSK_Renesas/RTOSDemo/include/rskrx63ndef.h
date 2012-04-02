
/******************************************************************************
* DISCLAIMER
* Please refer to http://www.renesas.com/disclaimer
******************************************************************************
  Copyright (C) 2011. Renesas Electronics Corp., All Rights Reserved.
*******************************************************************************
* File Name    : rsksh7216.h
* Version      : 1.00
* Description  : RSK RX63N board specific settings
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 12.09.2011 1.00    First Release
******************************************************************************/

#ifndef RSKRX63N_H
#define RSKRX63N_H

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

#define     XTAL_FREQUENCY  (12000000L)	
#define     PLL_MUL         (16)
#define     PLL_INPUT_FREQ_DIV         (1)
#define     ICLK_DIV        (2)
#define     PCLK_DIV        (4)
#define     BCLK_DIV        (4)
#define     PLL_FREQUENCY   (XTAL_FREQUENCY * (PLL_MUL / PLL_INPUT_FREQ_DIV))	
#define     ICLK_FREQUENCY  (PLL_FREQUENCY / ICLK_DIV)
#define     PCLK_FREQUENCY  (PLL_FREQUENCY / PCLK_DIV)
#define     BCLK_FREQUENCY  (PLL_FREQUENCY / BCLK_DIV)

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
#define		LED0			PORT0.PODR.BIT.B3
#define		LED1			PORT0.PODR.BIT.B5
#define		LED2			PORT1.PODR.BIT.B0
#define		LED3			PORT1.PODR.BIT.B1
//#define	    LED4			PORT6.DR.BIT.B0
//#define	    LED5			PORT7.DR.BIT.B3
#define		LED0_PDR        PORT0.PDR.BIT.B3
#define		LED1_PDR        PORT0.PDR.BIT.B5
#define		LED2_PDR        PORT1.PDR.BIT.B0
#define		LED3_PDR        PORT1.PDR.BIT.B1
//#define	    LED4_DDR        PORT6.DDR.BIT.B0
//#define	    LED5_DDR        PORT7.DDR.BIT.B3

/* 2x8 segment LCD */
#if 0
#define		INCLUDE_LCD		1
#define     LCD_RS          PORTJ.PODR.BIT.B1
#define     LCD_EN          PORTJ.PODR.BIT.B3
#define     LCD_DATA        PORTH.PODR.BYTE

#define     LCD_RS_DDR      PORTJ.PDR.BIT.B1
#define     LCD_EN_DDR      PORTJ.PDR.BIT.B3
#define     LCD_DATA_DDR    PORTH.PDR.BYTE
#endif


/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/



/* RSKRX63N_H */
#endif		

