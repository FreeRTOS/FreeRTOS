//*****************************************************************************
//
// hw_ints.h - Macros that define the interrupt assignment on Stellaris.
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

#ifndef __HW_INTS_H__
#define __HW_INTS_H__

//*****************************************************************************
//
// The following define the fault assignments.
//
//*****************************************************************************
#define FAULT_NMI               2           // NMI fault
#define FAULT_HARD              3           // Hard fault
#define FAULT_MPU               4           // MPU fault
#define FAULT_BUS               5           // Bus fault
#define FAULT_USAGE             6           // Usage fault
#define FAULT_SVCALL            11          // SVCall
#define FAULT_DEBUG             12          // Debug monitor
#define FAULT_PENDSV            14          // PendSV
#define FAULT_SYSTICK           15          // System Tick

//*****************************************************************************
//
// The following define the interrupt assignments.
//
//*****************************************************************************
#define INT_GPIOA               16          // GPIO Port A
#define INT_GPIOB               17          // GPIO Port B
#define INT_GPIOC               18          // GPIO Port C
#define INT_UART0               21          // UART0 Rx and Tx
#define INT_SSI                 23          // SSI Rx and Tx
#define INT_I2C                 24          // I2C Master and Slave
#define INT_WATCHDOG            34          // Watchdog timer
#define INT_TIMER0A             35          // Timer 0 subtimer A
#define INT_TIMER0B             36          // Timer 0 subtimer B
#define INT_TIMER1A             37          // Timer 1 subtimer A
#define INT_TIMER1B             38          // Timer 1 subtimer B
#define INT_COMP0               41          // Analog Comparator 0
#define INT_COMP1               42          // Analog Comparator 1
#define INT_SYSCTL              44          // System Control (PLL, OSC, BO)
#define INT_FLASH               45          // FLASH Control

//*****************************************************************************
//
// The total number of interrupts.
//
//*****************************************************************************
#define NUM_INTERRUPTS          46

//*****************************************************************************
//
// The total number of priority levels.
//
//*****************************************************************************
#define NUM_PRIORITY            8
#define NUM_PRIORITY_BITS       3

#endif // __HW_INTS_H__
