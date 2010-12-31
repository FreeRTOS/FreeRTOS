/** 
 * @file  hal_board.c
 * 
 * Copyright 2010 Texas Instruments, Inc.
******************************************************************************/
#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"

/**********************************************************************//**
 * @brief  Initializes ACLK, MCLK, SMCLK outputs on P11.0, P11.1, 
 *         and P11.2, respectively.
 * 
 * @param  none
 * 
 * @return none
 *************************************************************************/
void halBoardOutputSystemClock(void) //outputs clock to testpoints
{
  CLK_PORT_DIR |= 0x07;
  CLK_PORT_SEL |= 0x07;                           
}

/**********************************************************************//**
 * @brief  Stops the output of ACLK, MCLK, SMCLK on P11.0, P11.1, and P11.2.
 * 
 * @param  none
 * 
 * @return none
 *************************************************************************/
void halBoardStopOutputSystemClock(void)
{  
  CLK_PORT_OUT &= ~0x07;
  CLK_PORT_DIR |= 0x07;	
  CLK_PORT_SEL &= ~0x07;                 
}

/**********************************************************************//**
 * @brief  Initializes all GPIO configurations. 
 * 
 * @param  none
 * 
 * @return none
 *************************************************************************/
void halBoardInit(void)
{  
  //Tie unused ports
  PAOUT  = 0;
  PADIR  = 0xFFFF;  
  PASEL  = 0;
  PBOUT  = 0;  
  PBDIR  = 0xFFFF;
  PBSEL  = 0;
  PCOUT  = 0;    
  PCDIR  = 0xFFFF;
  PCSEL  = 0;  
  PDOUT  = 0;  
  PDDIR  = 0xFFFF;
  PDSEL  = 0x0003;  
  PEOUT  = 0;  
  PEDIR  = 0xFEFF;                          // P10.0 to USB RST pin, 
                                            // ...if enabled with J5
  PESEL  = 0;  
  P11OUT = 0;
  P11DIR = 0xFF;
  PJOUT  = 0;    
  PJDIR  = 0xFF;
  P11SEL = 0;
     
  AUDIO_PORT_OUT = AUDIO_OUT_PWR_PIN ;
  USB_PORT_DIR &= ~USB_PIN_RXD;             // USB RX Pin, Input with 
                                            // ...pulled down Resistor
  USB_PORT_OUT &= ~USB_PIN_RXD;
  USB_PORT_REN |= USB_PIN_RXD;
}
