/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.    
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : rskrx231def.h
* Device(s)    : R5F52318AxFP
* Tool-Chain   : CCRX
* H/W Platform : RSKRX231
* Description  : Defines macros relating to the RSKRX231 user LEDs and switches
***********************************************************************************************************************/
/**********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 01.06.2015 1.00     First Release
***********************************************************************************************************************/


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#ifndef RSKRX231_H
#define RSKRX231_H


/* General Values */
#define LED_ON          (0)
#define LED_OFF         (1)
#define SET_BIT_HIGH    (1)
#define SET_BIT_LOW     (0)
#define SET_BYTE_HIGH   (0xFF)
#define SET_BYTE_LOW    (0x00)

/* Switches */
#define SW1             (PORT3.PIDR.BIT.B1)
#define SW2             (PORT3.PIDR.BIT.B4)
#define SW3             (PORT0.PIDR.BIT.B7)

/* LED port settings */
#define LED0            (PORT1.PODR.BIT.B7)
#define LED1            (PORT5.PODR.BIT.B0)
#define LED2            (PORT5.PODR.BIT.B1)
#define LED3            (PORT5.PODR.BIT.B2)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global variables
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/

#endif

