

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


/*
 * cgc.h
 *
 *  Created on: 01 Oct 2011
 *      Author: RJW
 *              Reneses Electronics Europe Ltd
 */
 

#ifndef CGC_H_
#define CGC_H_

/******************************************************************************
 Function Prototypes
******************************************************************************/
void InitCGC(void);


/*****************************************************************************/
/*                                                                           */
/* Set the CGC (Clock Generation Circuit of the RX630 using the              */
/* following 7 STEPS                                                         */
/*                                                                           */
/*****************************************************************************/


/*****************************************************************************/
/*                                                                           */
/* STEP 1: System Clock Options                                              */
/*                                                                           */
/* Enter one of the CLK_SOURCE_ options into the                             */
/*                                                                           */
/*      #define     CLK_SOURCE          ( xxx )                              */
/* below.                                                                    */
/* This will be the clock source that the device will switch to as part of   */
/* HardwareSetup()                                                           */
/* Extra clocks can be enabled in STEP 3.                                    */
/*                                                                           */
/* For example                                                               */
/*      #define		CLK_SOURCE          (CLK_SOURCE_MAIN)                    */
/*                                                                           */
/*****************************************************************************/
#define     CLK_SOURCE_LOCO     0x0000
#define     CLK_SOURCE_HOCO     0x0100
#define     CLK_SOURCE_MAIN     0x0200
#define     CLK_SOURCE_SUB      0x0300
#define     CLK_SOURCE_PLL      0x0400

#define		CLK_SOURCE          (CLK_SOURCE_PLL)


/*****************************************************************************/
/*                                                                           */
/* STEP 2: External XTAL values                                              */
/*                                                                           */
/* If using the CLK_SOURCE_MAIN, CLK_SOURCE_SUB, CLK_SOURCE_PLL              */
/* enter the MAIN XTAL and SUB XTAL values here.                             */
/*                                                                           */
/* If using the PLL, enter the PLL multiplier and PLL frequency divder       */
/* Use the divider so that the input frequency into the PLL is in            */
/* the range of 4 MHz to 16 MHz.                                             */
/*                                                                           */
/* Use the multiplier so that the output frequency of the PLL is in          */
/* the range of 104MHz to 200Mhz                                             */
/*                                                                           */
/* The PLL frequency divider values are:                                     */
/*      /1, /2, /4                                                           */
/* The PLL muliplier values are:                                             */
/*      x8, x10, x12, x16, x20, x24, x25, x50                                */
/*                                                                           */
/* Example:                                                                  */
/*      XTAL = 12MHz                                                         */
/*      PLL Divider = 1                                                      */
/*                                                                           */
/*      Therefore, input into PLL = 12M / 1                                  */
/*                                = 12M                                      */
/*      PLL Multipler = 16                                                   */
/*                                                                           */
/*      Therefore, ouput of PLL = 12M x 16                                   */
/*                              = 192M                                       */
/*                                                                           */
/* NOTE: The maximum XTAL is 20MHz                                           */
/*****************************************************************************/
#define     XTAL_FREQUENCY      (12000000L)	
#define     PLL_MUL             (16)
#define     PLL_INPUT_FREQ_DIV  (1)

#define     SUB_FREQUENCY       (32768L)	


/*****************************************************************************/
/*                                                                           */
/* STEP 3: Enable the chosen clock source and any extra clock sources        */
/* Remeber to enable the clock source chosen in STEP 1.                      */
/* Foe example, if CLK_SOURCE_PLL has been chosen, set                       */
/* #define     ENABLE_PLL          (1)                                       */
/*                                                                           */
/*****************************************************************************/
#define     ENABLE_HOCO         (1)
#define     ENABLE_SUB          (0)
#define     ENABLE_MAIN         (0)
#define     ENABLE_PLL          (1)



/*****************************************************************************/
/*                                                                           */
/* STEP 4:                                                                   */
/*  Enter the Clock Divders for                                              */
/*      - FCLK_DIV, ICLK_DIV, BCLK_DIV, PCLKA_DIV, PCLKB_DIV                 */
/*  Valid values are 1, 2, 4, 8, 16, 32 and 64                               */
/*                                                                           */
/* The Clock Value being divided is:                                         */
/*  If LOCO, 125kHz                                                          */
/*  If HOCO, 50MHz                                                           */
/*  If SUB,  the value of SUB specified in STEP 2                            */
/*  If MAIN, the value of XTAL specified in STEP 2                           */
/*  If PLL,  the result of the XTAL, PLL Div, PLL Mul specified in STEP 2    */
/*****************************************************************************/
#define     FCLK_DIV            (4)
#define     ICLK_DIV            (2)
#define     BCLK_DIV            (4)
#define     PCLK1215_DIV        (2)             /* Do not change this        */
#define     PCLKB_DIV           (4)
#define     PCLK47_DIV          (2)             /* Do not change this        */
#define     PCLK03_DIV          (2)             /* Do not change this        */


/*****************************************************************************/
/*                                                                           */
/* STEP 5:                                                                   */
/*  Enter the Clock Divder for                                               */
/*      - IEBCK_DIV                                                          */
/*  Valid values are 2, 4, 6, 8, 16, 32 and 64                               */
/*                                                                           */
/* The Clock Value being divided is:                                         */
/*  If LOCO, 125kHz                                                          */
/*  If HOCO, 50MHz                                                           */
/*  If SUB,  the value of SUB specified in STEP 2                            */
/*  If MAIN, the value of XTAL specified in STEP 2                           */
/*  If PLL,  the result of the XTAL, PLL Div, PLL Mul specified in STEP 2    */
/*****************************************************************************/
#define     IEBCK_DIV           (2)


/*****************************************************************************/
/*                                                                           */
/* STEP 6:                                                                   */
/*  Enter the Clock Divder for                                               */
/*      - UCK_DIV                                                            */
/*  Valid values are 3, 4                                                    */
/*                                                                           */
/* The Clock Value being divided is:                                         */
/*  If LOCO, 125kHz                                                          */
/*  If HOCO, 50MHz                                                           */
/*  If SUB,  the value of SUB specified in STEP 2                            */
/*  If MAIN, the value of XTAL specified in STEP 2                           */
/*  If PLL,  the result of the XTAL, PLL Div, PLL Mul specified in STEP 2    */
/*****************************************************************************/
#define     UCK_DIV             (3)


/*****************************************************************************/
/*                                                                           */
/* STEP 7:                                                                   */
/*  Specify the use of BCLK pin                                              */
/*  To ENABLE,  set to (0)                                                   */
/*  To DISABLE, set to (1)                                                   */
/*                                                                           */
/*****************************************************************************/
#define     BCLK_PIN            (1)


/*****************************************************************************/
/* Clock configuration is now complete.                                      */
/*****************************************************************************/
#include "cgc_set.h"
#include "cgc_error.h"

#endif