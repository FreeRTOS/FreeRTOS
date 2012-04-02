/******************************************************************************
* File Name    : rsk7670def.h
* Version      : 1.0
* Device(s)    : SH2A/7670
* Tool-Chain   : Renesas SH2A V9+
* OS           : None
* H/W Platform : RSK+SH7670
* Description  : Defines for RSK2+SH7670 kit.
*******************************************************************************
* History      : DD.MM.YYYY Ver. Description
*              : 01.08.2009 1.00 MAB First Release
******************************************************************************/

/******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Technology Corp. and is only
* intended for use with Renesas products. No other uses are authorized.
* This software is owned by Renesas Technology Corp. and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
* REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY,
* INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
* PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY
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
******************************************************************************/
/* Copyright (C) 2008. Renesas Technology Corp.,       All Rights Reserved.  */
/* Copyright (C) 2009. Renesas Technology Europe Ltd., All Rights Reserved.  */
/*****************************************************************************/

#ifndef RSK7216DEF_H
#define RSK7216DEF_H

/******************************************************************************
Macro Defines
******************************************************************************/

/* General Values */
#define		LED_ON			(1)
#define 	LED_OFF			(0)
#define 	SET_BIT_HIGH	(1)
#define 	SET_BIT_LOW		(0)
#define 	SET_BYTE_HIGH	(0xFF)
#define 	SET_BYTE_LOW	(0x00)

/* Define switches to be polled if not available as interrupts */
#define		SW_ACTIVE		FALSE

#define 	SW1 			PORT.PDDRL.BIT.PD16DR //"IRQ0" PD16
#define 	SW2 			PORT.PADRL.BIT.PA20DR //"IRQ6" PA20


/* LEDs */
#define		LED0			PE.DR.BIT.B9 
#define		LED1			PE.DR.BIT.B11
#define		LED2			PE.DR.BIT.B12
#define		LED3			PE.DR.BIT.B13
#define		LED4			PE.DR.BIT.B14
#define		LED5			PE.DR.BIT.B15 

#define ID_LED1     1
#define ID_LED2     2
#define ID_LED3     4
#define ID_LED4     8
#define ID_LED5     16
#define ID_LED6     32
#define ID_LED_ALL  (ID_LED1 | ID_LED2 | ID_LED3 | ID_LED4 | ID_LED5 | ID_LED6)

#define PERIPHERAL_CLOCK_FREQUENCY  50000000UL

/******************************************************************************
Constant Macros
******************************************************************************/

#define BOARD_NAME  "SH7216 CPU BOARD"

/******************************************************************************
Public Functions
******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

extern void led_init(void);
extern void led_on(unsigned short ledno);
extern void led_off(unsigned short ledno);

#ifdef __cplusplus
}
#endif

#endif /* RSK7216DEF_H */

/******************************************************************************
End  Of File
******************************************************************************/