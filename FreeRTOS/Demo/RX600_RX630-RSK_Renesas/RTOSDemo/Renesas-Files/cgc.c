

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
 * cgc.c
 *
 *  Created on: 01 Oct 2011
 *      Author: RJW
 *              Reneses Electronics Europe Ltd
 */


/******************************************************************************
    System Includes                                                           
******************************************************************************/


/******************************************************************************
    User Includes                                                             
******************************************************************************/
#include    "iodefine.h"
#include    "cgc.h"


/*****************************************************************************/
/*                                                                           */
/* Configure the CGC (Clock Generation Circuit) of the RX630 using the       */
/* using the 7 STEPS specified in cgc.h                                      */
/*                                                                           */
/*****************************************************************************/


/******************************************************************************
   Function     : InitCGC
   Description 	: Initialises the CGC registers based upon the settings
                  made in file cgc.h
   Argument  	: none
   Return value : none
******************************************************************************/
void InitCGC(void)
{
    unsigned long i;
    
#if (ENABLE_SUB)
    SYSTEM.SOSCCR.BYTE = 0x00;              /* Sub-clock oscillator ON                      */
#else
    SYSTEM.SOSCCR.BYTE = 0x01;              /* Sub-clock oscillator OFF                     */
#endif

#if (ENABLE_HOCO)        												    
    SYSTEM.HOCOPCR.BYTE = 0x00;             /* HOCO PSU ON                                  */
    SYSTEM.HOCOCR.BYTE = 0x00;              /* HOCO ON                                      */
#else
    SYSTEM.HOCOPCR.BYTE = 0x01;             /* HOCO PSU OFF                                 */
    SYSTEM.HOCOCR.BYTE = 0x01;              /* HOCO OFF                                     */
#endif



#if (ENABLE_MAIN)									
    SYSTEM.MOSCWTCR.BYTE = 0x0e;            /* Main Clock Oscillator Wait Control Register  */
                                            /* 262144 states                                */
    SYSTEM.MOSCCR.BYTE = 0x00;				/* EXTAL ON                                     */
#else
    SYSTEM.MOSCCR.BYTE = 0x01;				/* EXTAL OFF                                    */
#endif    


#if (ENABLE_PLL)        
    SYSTEM.MOSCWTCR.BYTE = 0x0e;            /* Main Clock Oscillator Wait Control Register  */
                                            /* 262144 states                                */
    SYSTEM.MOSCCR.BYTE = 0x00;				/* EXTAL ON                                     */
    
    SYSTEM.PLLWTCR.BYTE = 0x0e;				/* PLL Wait Control Register                    */
                                            /* 2097152 states                               */
    
    SYSTEM.PLLCR2.BYTE = 0x01;				/* PLL OFF                                      */
    
    #if (PLL_INPUT_FREQ_DIV == 1)
        SYSTEM.PLLCR.BIT.PLIDIV = 0;
    #elif (PLL_INPUT_FREQ_DIV == 2)
        SYSTEM.PLLCR.BIT.PLIDIV = 1;
    #elif (PLL_INPUT_FREQ_DIV == 4)
        SYSTEM.PLLCR.BIT.PLIDIV = 2;
    #else
        SYSTEM.PLLCR.BIT.PLIDIV = 0;
    #endif
    SYSTEM.PLLCR.BIT.STC   = (PLL_MUL - 1);	

                                            /* External oscillation input selection         */
	SYSTEM.PLLCR2.BYTE = 0x00;				/* PLL ON                                       */
#else
    SYSTEM.PLLCR2.BYTE = 0x01;				/* PLL OFF                                      */
#endif
	
    for(i = 0; i<2500; i++)                 /* Wait for stabilisation of                    */
    {                                       /* HOCO, LOCO, PLL and main clock               */
    }                                       /* = 20ms                                       */
                                            /*   (2500 x 1/125kHz = 20ms)                   */
                                               
	    
    SYSTEM.SCKCR.LONG = FCLK_SCKCR      | 
                        ICLK_SCKCR      |
                        PSTOP1_SCKCR    |
                        BCLK_SCKCR      |
                        PCLK1215_SCKCR  |
                        PCLKB_SCKCR     |
                        PCLK47_SCKCR    |
                        PCLK03_SCKCR    ;
 
	
    SYSTEM.SCKCR2.WORD = UCK_SCKCR2    |
                         IEBCK_SCKCR2   ;		


	SYSTEM.SCKCR3.WORD = CLK_SOURCE;
}