/** ###################################################################
**     Filename  : Events.C
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
/* MODULE Events */


/*Including used modules for compilling procedure*/
#include "Cpu.h"
#include "Events.h"
#include "TickTimer.h"
#include "Byte1.h"
#include "COM0.h"

/*Include shared modules, which are used for whole project*/
#include "PE_Types.h"
#include "PE_Error.h"
#include "PE_Const.h"
#include "IO_Map.h"
#include "PE_Timer.h"

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
void TickTimer_OnInterrupt(void)
{
  /* Write your code here ... */
}


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
void COM0_OnError(void)
{
  /* Write your code here ... */
}

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
void COM0_OnRxChar(void)
{
  /* Write your code here ... */
}

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
void COM0_OnTxChar(void)
{
  /* Write your code here ... */
}

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
void COM0_OnFullRxBuf(void)
{
  /* Write your code here ... */
}

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
void COM0_OnFreeTxBuf(void)
{
  /* Write your code here ... */
}

/* END Events */

/*
** ###################################################################
**
**     This file was created by UNIS Processor Expert 03.33 for 
**     the Motorola HCS12 series of microcontrollers.
**
** ###################################################################
*/
