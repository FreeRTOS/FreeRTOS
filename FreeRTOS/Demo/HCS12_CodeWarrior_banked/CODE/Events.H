/** ###################################################################
**     Filename  : Events.H
**     Project   : RTOSDemo
**     Processor : MC9S12DP256BCPV
**     Beantype  : Events
**     Version   : Driver 01.01
**     Compiler  : Metrowerks HC12 C Compiler
**     Date/Time : 14/06/2005, 16:34
**     Abstract  :
**         This is user's event module.
**         Put your event handler code here.
**     Settings  :
**     Contents  :
**         TickTimer_OnInterrupt - void TickTimer_OnInterrupt(void);
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

void TickTimer_OnInterrupt(void);
/*
** ===================================================================
**     Event       :  TickTimer_OnInterrupt (module Events)
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


void COM0_OnError(void);
/*
** ===================================================================
**     Event       :  COM0_OnError (module Events)
**
**     From bean   :  COM0 [AsynchroSerial]
**     Description :
**         This event is called when a channel error (not the error
**         returned by a given method) occurs. The errors can be
**         read using <GetError> method.
**     Parameters  : None
**     Returns     : Nothing
** ===================================================================
*/

void COM0_OnRxChar(void);
/*
** ===================================================================
**     Event       :  COM0_OnRxChar (module Events)
**
**     From bean   :  COM0 [AsynchroSerial]
**     Description :
**         This event is called after a correct character is
**         received. This
**     Parameters  : None
**     Returns     : Nothing
** ===================================================================
*/

void COM0_OnTxChar(void);
/*
** ===================================================================
**     Event       :  COM0_OnTxChar (module Events)
**
**     From bean   :  COM0 [AsynchroSerial]
**     Description :
**         This event is called after a character is transmitted.
**     Parameters  : None
**     Returns     : Nothing
** ===================================================================
*/

void COM0_OnFullRxBuf(void);
/*
** ===================================================================
**     Event       :  COM0_OnFullRxBuf (module Events)
**
**     From bean   :  COM0 [AsynchroSerial]
**     Description :
**         This event is called when the input buffer is full.
**     Parameters  : None
**     Returns     : Nothing
** ===================================================================
*/

void COM0_OnFreeTxBuf(void);
/*
** ===================================================================
**     Event       :  COM0_OnFreeTxBuf (module Events)
**
**     From bean   :  COM0 [AsynchroSerial]
**     Description :
**         This event is called after the last character in output
**         buffer is transmitted.
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
