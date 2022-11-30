//*****************************************************************************
//
// hw_watchdog.h - Macros used when accessing the Watchdog Timer hardware.
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
// This is part of revision 523 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __HW_WATCHDOG_H__
#define __HW_WATCHDOG_H__

//*****************************************************************************
//
// The following define the offsets of the Watchdog Timer registers.
//
//*****************************************************************************
#define WDT_O_LOAD              0x00000000  // Load register
#define WDT_O_VALUE             0x00000004  // Current value register
#define WDT_O_CTL               0x00000008  // Control register
#define WDT_O_ICR               0x0000000C  // Interrupt clear register
#define WDT_O_RIS               0x00000010  // Raw interrupt status register
#define WDT_O_MIS               0x00000014  // Masked interrupt status register
#define WDT_O_TEST              0x00000418  // Test register
#define WDT_O_CAUSE             0x0000041C  // Cause register
#define WDT_O_LOCK              0x00000C00  // Lock register

//*****************************************************************************
//
// The following define the bit fields in the WDT_CTL register.
//
//*****************************************************************************
#define WDT_CTL_RESEN           0x00000002  // Enable reset output
#define WDT_CTL_INTEN           0x00000001  // Enable the WDT counter and int

//*****************************************************************************
//
// The following define the bit fields in the WDT_ISR, WDT_RIS, and WDT_MIS
// registers.
//
//*****************************************************************************
#define WDT_INT_TIMEOUT         0x00000001  // Watchdog timer expired

//*****************************************************************************
//
// The following define the bit fields in the WDT_TEST register.
//
//*****************************************************************************
#define WDT_TEST_STALL_EN       0x00000100  // Watchdog stall enable
#define WDT_TEST_TEST_EN        0x00000001  // Watchdog timer reset int test

//*****************************************************************************
//
// The following define the bit fields in the WDT_CAUSE register.
//
//*****************************************************************************
#define WDT_CAUSE_WDR           0x00000002  // Watchdog timer reset occurred
#define WDT_CAUSE_WDI           0x00000001  // Watchdog timer int occurred

//*****************************************************************************
//
// The following define the bit fields in the WDT_LOCK register.
//
//*****************************************************************************
#define WDT_LOCK_LOCKED         0x00000001  // Watchdog timer is locked
#define WDT_LOCK_UNLOCKED       0x00000000  // Watchdog timer is unlocked
#define WDT_LOCK_UNLOCK         0x1ACCE551  // Unlocks the watchdog timer

//*****************************************************************************
//
// The following define the reset values for the WDT registers.
//
//*****************************************************************************
#define WDT_RV_LOAD             0xFFFFFFFF  // Load register
#define WDT_RV_VALUE            0xFFFFFFFF  // Current value register
#define WDT_RV_CTL              0x00000000  // Control register
#define WDT_RV_RIS              0x00000000  // Raw interrupt status register
#define WDT_RV_MIS              0x00000000  // Masked interrupt status register
#define WDT_RV_LOCK             0x00000000  // Lock register

#endif // __HW_WATCHDOG_H__
