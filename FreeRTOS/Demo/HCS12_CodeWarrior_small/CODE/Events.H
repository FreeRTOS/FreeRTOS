/** ###################################################################
**     Filename  : Events.H
**     Project   : RTOSDemo
**     Processor : MC9S12C32CFU
**     Beantype  : Events
**     Version   : Driver 01.01
**     Compiler  : Metrowerks HC12 C Compiler
**     Date/Time : 17/05/2005, 08:36
**     Abstract  :
**         This is user's event module.
**         Put your event handler code here.
**     Settings  :
**     Contents  :
**         vTaskTickInterrupt - void vTaskTickInterrupt(void);
**
**     (c) Copyright UNIS, spol. s r.o. 1997-2002
**     UNIS, spol. s r.o.
**     Jundrovska 33
**     624 00 Brno
**     Czech Republic
**     http      : www.processorexpert.com
**     mail      : info@processorexpert.com
** ###################################################################*/

#ifndef __Events_H
#define __Events_H
/* MODULE Events */

#include "PE_Types.h"
#include "PE_Error.h"
#include "PE_Const.h"
#include "IO_Map.h"
#include "PE_Timer.h"

void vTaskTickInterrupt(void);
/*
** ===================================================================
**     Event       :  vTaskTickInterrupt (module Events)
**
**     From bean   :  TickTimer [TimerInt]
**     Description :
**         When a timer interrupt occurs this event is called (only
**         when the bean is enabled - "Enable" and the events are
**         enabled - "EnableEvent").
**     Parameters  : None
**     Returns     : Nothing
** ===================================================================
*/


void ButtonInterrupt_OnInterrupt(void);
/*
** ===================================================================
**     Event       :  ButtonInterrupt_OnInterrupt (module Events)
**
**     From bean   :  ButtonInterrupt [ExtInt]
**     Description :
**         This event is called when the active signal edge/level
**         occurs.
**     Parameters  : None
**     Returns     : Nothing
** ===================================================================
*/
/* END Events */
#endif /* __Events_H*/

/*
** ###################################################################
**
**     This file was created by UNIS Processor Expert 03.33 for 
**     the Motorola HCS12 series of microcontrollers.
**
** ###################################################################
*/
