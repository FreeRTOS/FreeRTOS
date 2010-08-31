
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
#define     XTAL_FREQUENCY  (12000000L)
#define     ICLK_MUL        (8)
#define     PCLK_MUL        (4)
#define     BCLK_MUL        (4)
#define     ICLK_FREQUENCY  (XTAL_FREQUENCY * ICLK_MUL)
#define     PCLK_FREQUENCY  (XTAL_FREQUENCY * PCLK_MUL)
#define     BCLK_FREQUENCY  (XTAL_FREQUENCY * BCLK_MUL)

#define     CMT0_CLK_SELECT (512)

/* General Values */
#define		LED_ON          (1)
#define 	LED_OFF			(0)

/* LEDs */
/*  Define LEDs to Port Numbers                                                     */
#define 	LED0			PORTD.DR.BIT.B0
#define 	LED1			PORTD.DR.BIT.B1
#define 	LED2			PORTD.DR.BIT.B2
#define 	LED3			PORTD.DR.BIT.B3
#define 	LED4			PORTD.DR.BIT.B4
#define 	LED5			PORTD.DR.BIT.B5
#define 	LED6			PORTD.DR.BIT.B6
#define 	LED7			PORTD.DR.BIT.B7
#define 	LED8			PORTE.DR.BIT.B0
#define 	LED9			PORTE.DR.BIT.B1
#define 	LED10			PORTE.DR.BIT.B2
#define 	LED11			PORTE.DR.BIT.B3

#define		LED0_DDR		PORTD.DDR.BIT.B0
#define		LED1_DDR		PORTD.DDR.BIT.B1
#define 	LED2_DDR		PORTD.DDR.BIT.B2
#define 	LED3_DDR		PORTD.DDR.BIT.B3
#define 	LED4_DDR		PORTD.DDR.BIT.B4
#define 	LED5_DDR		PORTD.DDR.BIT.B5
#define 	LED6_DDR		PORTD.DDR.BIT.B6
#define 	LED7_DDR		PORTD.DDR.BIT.B7
#define 	LED8_DDR		PORTE.DDR.BIT.B0
#define 	LED9_DDR		PORTE.DDR.BIT.B1
#define 	LED10_DDR		PORTE.DDR.BIT.B2
#define 	LED11_DDR		PORTE.DDR.BIT.B3




/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/



/* RSKRX62N_H */
#endif		

