/** ###################################################################
**     Filename  : RTOSDemo.C
**     Project   : RTOSDemo
**     Processor : MC9S12C32CFU
**     Version   : Driver 01.05
**     Compiler  : Metrowerks HC12 C Compiler
**     Date/Time : 10/05/2005, 11:11
**     Abstract  :
**         Main module. 
**         Here is to be placed user's code.
**     Settings  :
**     Contents  :
**         No public methods
**
**     (c) Copyright UNIS, spol. s r.o. 1997-2002
**     UNIS, spol. s r.o.
**     Jundrovska 33
**     624 00 Brno
**     Czech Republic
**     http      : www.processorexpert.com
**     mail      : info@processorexpert.com
** ###################################################################*/
/* MODULE RTOSDemo */

/* Including used modules for compilling procedure */
#include "Cpu.h"
#include "Events.h"
#include "Byte1.h"
#include "TickTimer.h"
#include "ButtonInterrupt.h"
/* Include shared modules, which are used for whole project */
#include "PE_Types.h"
#include "PE_Error.h"
#include "PE_Const.h"
#include "IO_Map.h"

extern void vMain( void );

void main(void)
{
  /*** Processor Expert internal initialization. DON'T REMOVE THIS CODE!!! ***/
  PE_low_level_init();
  /*** End of Processor Expert internal initialization.                    ***/

  /*Write your code here*/
  
  /* Just jump to the real main(). */
  __asm
  {
  	 jmp vMain
  }
  
  /*** Processor Expert end of main routine. DON'T MODIFY THIS CODE!!! ***/
    for(;;);
  /*** Processor Expert end of main routine. DON'T WRITE CODE BELOW!!! ***/
} /*** End of main routine. DO NOT MODIFY THIS TEXT!!! ***/

/* END RTOSDemo */
/*
** ###################################################################
**
**     This file was created by UNIS Processor Expert 03.33 for 
**     the Motorola HCS12 series of microcontrollers.
**
** ###################################################################
*/
