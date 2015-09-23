/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_userdefine.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file includes user definition.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef _USER_DEF_H
#define _USER_DEF_H

/***********************************************************************************************************************
User definitions
***********************************************************************************************************************/

/* Start user code for function. Do not edit comment generated here */

#define MPC_PFSWE_WRITE_ENABLE (0x00)
#define MPC_PFS_WRITE_ENABLE   (0x40)
#define MPC_PFS_WRITE_DISABLE  (0x80)

#define MPC_IRQ_DISABLE        (0)
#define MPC_IRQ_ENABLE         (1)

/* Define LED states */
#define LED_ON                  (1U)
#define LED_OFF                 (0U)

/* Define user LEDs mode register pins */
#define LED0_MODE               (PORTF.PMR.BIT.B7)
#define LED1_MODE               (PORT5.PMR.BIT.B6)
#define LED2_MODE               (PORT7.PMR.BIT.B7)
#define LED3_MODE               (PORTA.PMR.BIT.B0)

/* Define user LEDs direction's pins */
#define LED0_DIR                (PORTF.PDR.BIT.B7)
#define LED1_DIR                (PORT5.PDR.BIT.B6)
#define LED2_DIR                (PORT7.PDR.BIT.B7)
#define LED3_DIR                (PORTA.PDR.BIT.B0)

/* Define user LEDs */
#define LED0                    (PORTF.PODR.BIT.B7)
#define LED1                    (PORT5.PODR.BIT.B6)
#define LED2                    (PORT7.PODR.BIT.B7)
#define LED3                    (PORTA.PODR.BIT.B0)

void R_MPC_WriteEnable (void);
void R_MPC_WriteDisable (void);

extern void r_set_exception_handler(void);

/* End user code. Do not edit comment generated here */
#endif