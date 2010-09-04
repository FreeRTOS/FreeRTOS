
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

#ifndef RDKRX62N_H
#define RDKRX62N_H

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
#define 	SET_BIT_HIGH	(1)
#define 	SET_BIT_LOW		(0)
#define 	SET_BYTE_HIGH	(0xFF)
#define 	SET_BYTE_LOW	(0x00)

/* Define switches to be polled if not available as interrupts */
#define		SW_ACTIVE		FALSE
#define     SW1             PORT4.PORT.BIT.B0
#define     SW2             PORT4.PORT.BIT.B1
#define     SW3             PORT4.PORT.BIT.B2
#define     SW1_DDR         PORT4.DDR.BIT.B0
#define     SW2_DDR         PORT4.DDR.BIT.B1
#define     SW3_DDR         PORT4.DDR.BIT.B2
#define     SW1_ICR         PORT4.ICR.BIT.B0
#define     SW2_ICR         PORT4.ICR.BIT.B1
#define     SW3_ICR         PORT4.ICR.BIT.B2

/* LEDs */
#define     LED4            PORTD.DR.BIT.B5
#define     LED5            PORTE.DR.BIT.B3
#define     LED6            PORTD.DR.BIT.B2
#define     LED7            PORTE.DR.BIT.B0
#define     LED8            PORTD.DR.BIT.B4
#define     LED9            PORTE.DR.BIT.B2
#define     LED10           PORTD.DR.BIT.B1
#define     LED11           PORTD.DR.BIT.B7
#define     LED12           PORTD.DR.BIT.B3
#define     LED13           PORTE.DR.BIT.B1
#define     LED14           PORTD.DR.BIT.B0
#define     LED15           PORTD.DR.BIT.B6

#define     LED4_DDR        PORTD.DDR.BIT.B5
#define     LED5_DDR        PORTE.DDR.BIT.B3
#define     LED6_DDR        PORTD.DDR.BIT.B2
#define     LED7_DDR        PORTE.DDR.BIT.B0
#define     LED8_DDR        PORTD.DDR.BIT.B4
#define     LED9_DDR        PORTE.DDR.BIT.B2
#define     LED10_DDR       PORTD.DDR.BIT.B1
#define     LED11_DDR       PORTD.DDR.BIT.B7
#define     LED12_DDR       PORTD.DDR.BIT.B3
#define     LED13_DDR       PORTE.DDR.BIT.B1
#define     LED14_DDR       PORTD.DDR.BIT.B0
#define     LED15_DDR       PORTD.DDR.BIT.B6




/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/



/* RDKRX62N_H */
#endif		

