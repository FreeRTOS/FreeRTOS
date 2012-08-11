
/******************************************************************************
* DISCLAIMER
* Please refer to http://www.renesas.com/disclaimer
******************************************************************************
  Copyright (C) 2008. Renesas Technology Corp., All Rights Reserved.
*******************************************************************************
* File Name    : rskrx630def.h
* Version      : 1.00
* Description  : RSK RX630 board specific settings
******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 06.10.2009 1.00    First Release
******************************************************************************/

#ifndef RSKRX630_H
#define RSKRX630_H

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "cgc.h"

/******************************************************************************
Typedef definitions
******************************************************************************/

/******************************************************************************
Macro definitions
******************************************************************************/

/* System Clock Settings */
/* Clock settings defined in CGC_SET.H */
#if 0
#define     XTAL_FREQUENCY  (12000000L)
#define     ICLK_MUL        (8)
#define     PCLK_MUL        (4)
#define     BCLK_MUL        (4)
#define     ICLK_FREQUENCY  (XTAL_FREQUENCY * ICLK_MUL)
#define     PCLK_FREQUENCY  (XTAL_FREQUENCY * PCLK_MUL)
#define     BCLK_FREQUENCY  (XTAL_FREQUENCY * BCLK_MUL)
#endif

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
#define 	SW1 			PORT3.PODR.BIT.B2
#define 	SW2 			PORT4.PODR.BIT.B4
#define     SW3             PORT0.PODR.BIT.B7
#define 	SW1_PDR			PORT3.PDR.BIT.B2
#define 	SW2_PDR			PORT4.PDR.BIT.B4
#define     SW3_PDR         PORT0.PDR.BIT.B7

/* LEDs */
#define		LED0			PORTC.PODR.BIT.B5
#define		LED1			PORT2.PODR.BIT.B4
#define		LED2			PORTC.PODR.BIT.B2
#define		LED3			PORT1.PODR.BIT.B7
#define		LED0_PDR        PORTC.PDR.BIT.B5
#define		LED1_PDR        PORT2.PDR.BIT.B4
#define		LED2_PDR        PORTC.PDR.BIT.B2
#define		LED3_PDR        PORT1.PDR.BIT.B7

/* 2x8 segment LCD */
#define     LCD_RS          PORTJ.PODR.BIT.B3
#define     LCD_EN          PORT3.PODR.BIT.B3
#define     LCD_DATA        PORTE.PODR.BYTE
#define     LCD_RS_PDR      PORTJ.PDR.BIT.B3
#define     LCD_EN_PDR      PORT3.PDR.BIT.B3
#define     LCD_DATA_PDR    PORTE.PDR.BYTE



/******************************************************************************
Variable Externs
******************************************************************************/

/******************************************************************************
Functions Prototypes
******************************************************************************/



/* RSKRX62N_H */
#endif		

