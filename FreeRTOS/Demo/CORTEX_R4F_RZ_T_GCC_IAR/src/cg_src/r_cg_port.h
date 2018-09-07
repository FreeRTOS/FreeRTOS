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
* File Name    : r_cg_port.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for Port module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef PORT_H
#define PORT_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    Port Direction Register (PDR)
*/
/* Pmn Direction Control (B0 - B15) */
#define _Pm0_MODE_NOT_USED             (0x0000U) /* Pm0 not used (Hi-z input protection) */
#define _Pm0_MODE_INPUT                (0x0002U) /* Pm0 as input */
#define _Pm0_MODE_OUTPUT               (0x0003U) /* Pm0 as output */
#define _Pm1_MODE_NOT_USED             (0x0000U) /* Pm1 not used (Hi-z input protection) */
#define _Pm1_MODE_INPUT                (0x0008U) /* Pm1 as input */
#define _Pm1_MODE_OUTPUT               (0x000CU) /* Pm1 as output */
#define _Pm2_MODE_NOT_USED             (0x0000U) /* Pm2 not used (Hi-z input protection) */
#define _Pm2_MODE_INPUT                (0x0020U) /* Pm2 as input */
#define _Pm2_MODE_OUTPUT               (0x0030U) /* Pm2 as output */
#define _Pm3_MODE_NOT_USED             (0x0000U) /* Pm3 not used (Hi-z input protection) */
#define _Pm3_MODE_INPUT                (0x0080U) /* Pm3 as input */
#define _Pm3_MODE_OUTPUT               (0x00C0U) /* Pm3 as output */
#define _Pm4_MODE_NOT_USED             (0x0000U) /* Pm4 not used (Hi-z input protection) */
#define _Pm4_MODE_INPUT                (0x0200U) /* Pm4 as input */
#define _Pm4_MODE_OUTPUT               (0x0300U) /* Pm4 as output */
#define _Pm5_MODE_NOT_USED             (0x0000U) /* Pm5 not used (Hi-z input protection) */
#define _Pm5_MODE_INPUT                (0x0800U) /* Pm5 as input */
#define _Pm5_MODE_OUTPUT               (0x0C00U) /* Pm5 as output */
#define _Pm6_MODE_NOT_USED             (0x0000U) /* Pm6 not used (Hi-z input protection) */
#define _Pm6_MODE_INPUT                (0x2000U) /* Pm6 as input */
#define _Pm6_MODE_OUTPUT               (0x3000U) /* Pm6 as output */
#define _Pm7_MODE_NOT_USED             (0x0000U) /* Pm7 not used (Hi-z input protection) */
#define _Pm7_MODE_INPUT                (0x8000U) /* Pm7 as input */
#define _Pm7_MODE_OUTPUT               (0xC000U) /* Pm7 as output */

/*
    Port Output Data Register (PODR)
*/
/* Pmn Output Data Store (B0 - B7) */
#define _Pm0_OUTPUT_0                  (0x00U) /* Output low at B0 */
#define _Pm0_OUTPUT_1                  (0x01U) /* Output high at B0 */
#define _Pm1_OUTPUT_0                  (0x00U) /* Output low at B1 */
#define _Pm1_OUTPUT_1                  (0x02U) /* Output high at B1 */
#define _Pm2_OUTPUT_0                  (0x00U) /* Output low at B2 */
#define _Pm2_OUTPUT_1                  (0x04U) /* Output high at B2 */
#define _Pm3_OUTPUT_0                  (0x00U) /* Output low at B3 */
#define _Pm3_OUTPUT_1                  (0x08U) /* Output high at B3 */
#define _Pm4_OUTPUT_0                  (0x00U) /* Output low at B4 */
#define _Pm4_OUTPUT_1                  (0x10U) /* Output high at B4 */
#define _Pm5_OUTPUT_0                  (0x00U) /* Output low at B5 */
#define _Pm5_OUTPUT_1                  (0x20U) /* Output high at B5 */
#define _Pm6_OUTPUT_0                  (0x00U) /* Output low at B6 */
#define _Pm6_OUTPUT_1                  (0x40U) /* Output high at B6 */
#define _Pm7_OUTPUT_0                  (0x00U) /* Output low at B7 */
#define _Pm7_OUTPUT_1                  (0x80U) /* Output high at B7 */

/*
    Pull-Up/Pull-Down Control Register (PCR)
*/
/* Pmn Input Pull-Up Resistor Control (B0 - B15) */
#define _Pm0_PULLUPDOWN_DISABLE        (0x0000U) /* Pm0 pull-up resistor and pull-down resistor not connected */
#define _Pm0_PULLUPDOWN_PULLDOWN_ON    (0x0001U) /* Pm0 pull-down resistor connected */
#define _Pm0_PULLUPDOWN_PULLUP_ON      (0x0002U) /* Pm0 pull-up resistor connected */
#define _Pm1_PULLUPDOWN_DISABLE        (0x0000U) /* Pm1 pull-up resistor and pull-down resistor not connected */
#define _Pm1_PULLUPDOWN_PULLDOWN_ON    (0x0004U) /* Pm1 pull-down resistor connected */
#define _Pm1_PULLUPDOWN_PULLUP_ON      (0x0008U) /* Pm1 pull-up resistor connected */
#define _Pm2_PULLUPDOWN_DISABLE        (0x0000U) /* Pm2 pull-up resistor and pull-down resistor not connected */
#define _Pm2_PULLUPDOWN_PULLDOWN_ON    (0x0010U) /* Pm2 pull-down resistor connected */
#define _Pm2_PULLUPDOWN_PULLUP_ON      (0x0020U) /* Pm2 pull-up resistor connected */
#define _Pm3_PULLUPDOWN_DISABLE        (0x0000U) /* Pm3 pull-up resistor and pull-down resistor not connected */
#define _Pm3_PULLUPDOWN_PULLDOWN_ON    (0x0040U) /* Pm3 pull-down resistor connected */
#define _Pm3_PULLUPDOWN_PULLUP_ON      (0x0080U) /* Pm3 pull-up resistor connected */
#define _Pm4_PULLUPDOWN_DISABLE        (0x0000U) /* Pm4 pull-up resistor and pull-down resistor not connected */
#define _Pm4_PULLUPDOWN_PULLDOWN_ON    (0x0100U) /* Pm4 pull-down resistor connected */
#define _Pm4_PULLUPDOWN_PULLUP_ON      (0x0200U) /* Pm4 pull-up resistor connected */
#define _Pm5_PULLUPDOWN_DISABLE        (0x0000U) /* Pm5 pull-up resistor and pull-down resistor not connected */
#define _Pm5_PULLUPDOWN_PULLDOWN_ON    (0x0400U) /* Pm5 pull-down resistor connected */
#define _Pm5_PULLUPDOWN_PULLUP_ON      (0x0800U) /* Pm5 pull-up resistor connected */
#define _Pm6_PULLUPDOWN_DISABLE        (0x0000U) /* Pm6 pull-up resistor and pull-down resistor not connected */
#define _Pm6_PULLUPDOWN_PULLDOWN_ON    (0x1000U) /* Pm6 pull-down resistor connected */
#define _Pm6_PULLUPDOWN_PULLUP_ON      (0x2000U) /* Pm6 pull-up resistor connected */
#define _Pm7_PULLUPDOWN_DISABLE        (0x0000U) /* Pm7 pull-up resistor and pull-down resistor not connected */
#define _Pm7_PULLUPDOWN_PULLDOWN_ON    (0x4000U) /* Pm7 pull-down resistor connected */
#define _Pm7_PULLUPDOWN_PULLUP_ON      (0x8000U) /* Pm7 pull-up resistor connected */

/*
    Drive Capacity Control Register (DSCR)
*/
/* P10 Drive Capacity Control (B0) */
#define _Pm0_HIDRV_OFF                 (0x0000U) /* P10 Normal drive output */
#define _Pm0_HIDRV_ON                  (0x0001U) /* P10 High-drive output */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_PORT_Create(void);

/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif