//*****************************************************************************
//
// watchdog.h - Prototypes for the Watchdog Timer API
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
// This is part of revision 991 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __WATCHDOG_H__
#define __WATCHDOG_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern tBoolean WatchdogRunning(unsigned long ulBase);
extern void WatchdogEnable(unsigned long ulBase);
extern void WatchdogResetEnable(unsigned long ulBase);
extern void WatchdogResetDisable(unsigned long ulBase);
extern void WatchdogLock(unsigned long ulBase);
extern void WatchdogUnlock(unsigned long ulBase);
extern tBoolean WatchdogLockState(unsigned long ulBase);
extern void WatchdogReloadSet(unsigned long ulBase, unsigned long ulLoadVal);
extern unsigned long WatchdogReloadGet(unsigned long ulBase);
extern unsigned long WatchdogValueGet(unsigned long ulBase);
extern void WatchdogIntRegister(unsigned long ulBase, void(*pfnHandler)(void));
extern void WatchdogIntUnregister(unsigned long ulBase);
extern void WatchdogIntEnable(unsigned long ulBase);
extern unsigned long WatchdogIntStatus(unsigned long ulBase, tBoolean bMasked);
extern void WatchdogIntClear(unsigned long ulBase);
extern void WatchdogStallDisable(unsigned long ulBase);
extern void WatchdogStallDisable(unsigned long ulBase);

#ifdef __cplusplus
}
#endif

#endif // __WATCHDOG_H__
