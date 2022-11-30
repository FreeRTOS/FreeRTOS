//*****************************************************************************
//
// timer.h - Prototypes for the timer module
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
// This is part of revision 635 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __TIMER_H__
#define __TIMER_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Values that can be passed to TimerConfigure as the ulConfig parameter.
//
//*****************************************************************************
#define TIMER_CFG_32_BIT_OS     0x00000001  // 32-bit one-shot timer
#define TIMER_CFG_32_BIT_PER    0x00000002  // 32-bit periodic timer
#define TIMER_CFG_32_RTC        0x01000000  // 32-bit RTC timer
#define TIMER_CFG_16_BIT_PAIR   0x04000000  // Two 16-bit timers
#define TIMER_CFG_A_ONE_SHOT    0x00000001  // Timer A one-shot timer
#define TIMER_CFG_A_PERIODIC    0x00000002  // Timer A periodic timer
#define TIMER_CFG_A_CAP_COUNT   0x00000003  // Timer A event counter
#define TIMER_CFG_A_CAP_TIME    0x00000007  // Timer A event timer
#define TIMER_CFG_A_PWM         0x0000000A  // Timer A PWM output
#define TIMER_CFG_B_ONE_SHOT    0x00000100  // Timer B one-shot timer
#define TIMER_CFG_B_PERIODIC    0x00000200  // Timer B periodic timer
#define TIMER_CFG_B_CAP_COUNT   0x00000300  // Timer B event counter
#define TIMER_CFG_B_CAP_TIME    0x00000700  // Timer B event timer
#define TIMER_CFG_B_PWM         0x00000A00  // Timer B PWM output

//*****************************************************************************
//
// Values that can be passed to TimerIntEnable, TimerIntDisable, and
// TimerIntClear as the ulIntFlags parameter, and returned from TimerIntStatus.
//
//*****************************************************************************
#define TIMER_CAPB_EVENT        0x00000400  // CaptureB event interrupt
#define TIMER_CAPB_MATCH        0x00000200  // CaptureB match interrupt
#define TIMER_TIMB_TIMEOUT      0x00000100  // TimerB time out interrupt
#define TIMER_RTC_MATCH         0x00000008  // RTC interrupt mask
#define TIMER_CAPA_EVENT        0x00000004  // CaptureA event interrupt
#define TIMER_CAPA_MATCH        0x00000002  // CaptureA match interrupt
#define TIMER_TIMA_TIMEOUT      0x00000001  // TimerA time out interrupt

//*****************************************************************************
//
// Values that can be passed to TimerControlEvent as the ulEvent parameter.
//
//*****************************************************************************
#define TIMER_EVENT_POS_EDGE    0x00000000  // Count positive edges
#define TIMER_EVENT_NEG_EDGE    0x00000404  // Count negative edges
#define TIMER_EVENT_BOTH_EDGES  0x00000C0C  // Count both edges

//*****************************************************************************
//
// Values that can be passed to most of the timer APIs as the ulTimer
// parameter.
//
//*****************************************************************************
#define TIMER_A                 0x000000ff  // Timer A
#define TIMER_B                 0x0000ff00  // Timer B
#define TIMER_BOTH              0x0000ffff  // Timer Both

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern void TimerEnable(unsigned long ulBase, unsigned long ulTimer);
extern void TimerDisable(unsigned long ulBase, unsigned long ulTimer);
extern void TimerConfigure(unsigned long ulBase, unsigned long ulConfig);
extern void TimerControlLevel(unsigned long ulBase, unsigned long ulTimer,
                              tBoolean bInvert);
extern void TimerControlTrigger(unsigned long ulBase, unsigned long ulTimer,
                                tBoolean bEnable);
extern void TimerControlEvent(unsigned long ulBase, unsigned long ulTimer,
                              unsigned long ulEvent);
extern void TimerControlStall(unsigned long ulBase, unsigned long ulTimer,
                              tBoolean bStall);
extern void TimerRTCEnable(unsigned long ulBase);
extern void TimerRTCDisable(unsigned long ulBase);
extern void TimerPrescaleSet(unsigned long ulBase, unsigned long ulTimer,
                             unsigned long ulValue);
extern unsigned long TimerPrescaleGet(unsigned long ulBase,
                                      unsigned long ulTimer);
extern void TimerPrescaleMatchSet(unsigned long ulBase, unsigned long ulTimer,
                                  unsigned long ulValue);
extern unsigned long TimerPrescaleMatchGet(unsigned long ulBase,
                                           unsigned long ulTimer);
extern void TimerLoadSet(unsigned long ulBase, unsigned long ulTimer,
                         unsigned long ulValue);
extern unsigned long TimerLoadGet(unsigned long ulBase, unsigned long ulTimer);
extern unsigned long TimerValueGet(unsigned long ulBase,
                                   unsigned long ulTimer);
extern void TimerMatchSet(unsigned long ulBase, unsigned long ulTimer,
                          unsigned long ulValue);
extern unsigned long TimerMatchGet(unsigned long ulBase,
                                   unsigned long ulTimer);
extern void TimerIntRegister(unsigned long ulBase, unsigned long ulTimer,
                             void (*pfnHandler)(void));
extern void TimerIntUnregister(unsigned long ulBase, unsigned long ulTimer);
extern void TimerIntEnable(unsigned long ulBase, unsigned long ulIntFlags);
extern void TimerIntDisable(unsigned long ulBase, unsigned long ulIntFlags);
extern unsigned long TimerIntStatus(unsigned long ulBase, tBoolean bMasked);
extern void TimerIntClear(unsigned long ulBase, unsigned long ulIntFlags);
extern void TimerQuiesce(unsigned long ulBase);

#ifdef __cplusplus
}
#endif

#endif // __TIMER_H__
