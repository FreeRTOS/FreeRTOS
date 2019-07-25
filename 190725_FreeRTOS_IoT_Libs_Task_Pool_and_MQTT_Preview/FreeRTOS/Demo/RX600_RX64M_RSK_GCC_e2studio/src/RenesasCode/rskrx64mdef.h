/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only 
* intended for use with Renesas products. No other uses are authorized. This 
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE 
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*******************************************************************************/
/*******************************************************************************
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.    */
/*******************************************************************************
* File Name     : rskrx64mdef.h
* Version       : 1.00
* Device        : R5F564ML
* Tool-Chain    : Renesas RX Standard 2.01.0
* H/W Platform  : RSK+RX64M
* Description   : Defines macros relating to the RX64M user LEDs and switches
*******************************************************************************/
/*******************************************************************************
* History       : 20 Mar. 2014 Ver. 0.00 Alpha Release
*******************************************************************************/

/*******************************************************************************
* Macro Definitions
*******************************************************************************/
/* Multiple inclusion prevention macro */
#ifndef RSKRX64MDEF_H
#define RSKRX64MDEF_H

/*******************************************************************************
* User Includes (Project Level Includes)
*******************************************************************************/

/* General Values */
#define LED_ON          (0)
#define LED_OFF         (1)
#define SET_BIT_HIGH    (1)
#define SET_BIT_LOW     (0)
#define SET_BYTE_HIGH   (0xFF)
#define SET_BYTE_LOW    (0x00)
#define OUTPUT_PIN      (1)
#define INPUT_PIN       (0)

/* Switch port pins data direction */
#define SW1_PIN_DIR     (PORT1.PDR.BIT.B5)
#define SW2_PIN_DIR     (PORT1.PDR.BIT.B2)
#define SW3_PIN_DIR     (PORT0.PDR.BIT.B7)

/* Switches */
#define SW1             (PORT1.PIDR.BIT.B5)
#define SW2             (PORT1.PIDR.BIT.B2)
#define SW3             (PORT0.PIDR.BIT.B7)

/* LED data direction */
#define LED0_PIN_DIR    (PORT0.PDR.BIT.B3)
#define LED1_PIN_DIR    (PORT0.PDR.BIT.B5)
#define LED2_PIN_DIR    (PORT2.PDR.BIT.B6)
#define LED3_PIN_DIR    (PORT2.PDR.BIT.B7)

/* LED ouptut pin settings */
#define LED0			(PORT0.PODR.BIT.B3)
#define LED1            (PORT0.PODR.BIT.B5)
#define LED2            (PORT2.PODR.BIT.B6)
#define LED3            (PORT2.PODR.BIT.B7)

/* End of multiple inclusion prevention macro */
#endif
