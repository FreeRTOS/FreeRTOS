/** 
 * @file  hal_buttons.c
 * 
 * Copyright 2010 Texas Instruments, Inc.
***************************************************************************/
#include "msp430.h"
#include "hal_MSP-EXP430F5438.h"

/**********************************************************************//**
 * @brief  Initializes the GPIO ports to act as buttons.
 * 
 * @param  buttonsMask The mask that specifies the button pins.
 * 
 * @return none
 *************************************************************************/   
void halButtonsInit(unsigned char buttonsMask)
{  
  BUTTON_PORT_OUT |= buttonsMask;
  BUTTON_PORT_DIR &= ~buttonsMask;
  BUTTON_PORT_REN |= buttonsMask; 
  BUTTON_PORT_SEL &= ~buttonsMask;       
}

/**********************************************************************//**
 * @brief  Returns LOW for the buttons pressed.
 * 
 * @param  none
 * 
 * @return The buttons that have been pressed, identified by a bit = 0. 
 *************************************************************************/
unsigned char halButtonsPressed(void)
{
  unsigned char value;
  value = BUTTON_PORT_IN;
  return (0xFF - value);                    //Low==ButtonPressed
}

/**********************************************************************//**
 * @brief  Enables button interrupt(s) with low to high transitions.
 * 
 * @param  buttonIntEnableMask The button pin(s) for which the interrupt(s) 
 *                             should be enabled.
 * 
 * @return none
 *************************************************************************/
void halButtonsInterruptEnable(unsigned char buttonIntEnableMask)
{
  BUTTON_PORT_IES &= ~buttonIntEnableMask;
  BUTTON_PORT_IFG &= ~buttonIntEnableMask;
  BUTTON_PORT_IE |= buttonIntEnableMask;
}

/**********************************************************************//**
 * @brief  Disables button interrupts 
 * 
 * @param  buttonIntEnableMask The button pin(s) for which the interrupt(s)
 *                             should be disabled. 
 * 
 * @return none
 *************************************************************************/
void halButtonsInterruptDisable(unsigned char buttonIntEnableMask)
{
  BUTTON_PORT_IE &= ~buttonIntEnableMask;
}

/**********************************************************************//**
 * @brief  Clears the button GPIO settings, disables the buttons. 
 * 
 * @param  none
 *************************************************************************/
void halButtonsShutDown()
{
  //All output, outputting 0s
  BUTTON_PORT_OUT &= ~(BUTTON_ALL);
  BUTTON_PORT_DIR |= BUTTON_ALL;             
}
