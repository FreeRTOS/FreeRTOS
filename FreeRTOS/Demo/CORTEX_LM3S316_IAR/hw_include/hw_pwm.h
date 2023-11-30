//*****************************************************************************
//
// hw_pwm.h - Defines and Macros for Pulse Width Modulation (PWM) ports
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

#ifndef __HW_PWM_H__
#define __HW_PWM_H__

//*****************************************************************************
//
// PWM Module Register Offsets.
//
//*****************************************************************************
#define PWM_O_CTL               0x00000000  // PWM Master Control register
#define PWM_O_SYNC              0x00000004  // PWM Time Base Sync register
#define PWM_O_ENABLE            0x00000008  // PWM Output Enable register
#define PWM_O_INVERT            0x0000000C  // PWM Output Inversion register
#define PWM_O_FAULT             0x00000010  // PWM Output Fault register
#define PWM_O_INTEN             0x00000014  // PWM Interrupt Enable register
#define PWM_O_RIS               0x00000018  // PWM Interrupt Raw Status reg.
#define PWM_O_ISC               0x0000001C  // PWM Interrupt Status register
#define PWM_O_STATUS            0x00000020  // PWM Status register

//*****************************************************************************
//
// The following define the bit fields in the PWM Master Control register.
//
//*****************************************************************************
#define PWM_CTL_GLOBAL_SYNC2    0x00000004  // Global sync generator 2
#define PWM_CTL_GLOBAL_SYNC1    0x00000002  // Global sync generator 1
#define PWM_CTL_GLOBAL_SYNC0    0x00000001  // Global sync generator 0

//*****************************************************************************
//
// The following define the bit fields in the PWM Time Base Sync register.
//
//*****************************************************************************
#define PWM_SYNC_SYNC2          0x00000004  // Reset generator 2 counter
#define PWM_SYNC_SYNC1          0x00000002  // Reset generator 1 counter
#define PWM_SYNC_SYNC0          0x00000001  // Reset generator 0 counter

//*****************************************************************************
//
// The following define the bit fields in the PWM Output Enable register.
//
//*****************************************************************************
#define PWM_ENABLE_PWM5EN       0x00000020  // PWM5 pin enable
#define PWM_ENABLE_PWM4EN       0x00000010  // PWM4 pin enable
#define PWM_ENABLE_PWM3EN       0x00000008  // PWM3 pin enable
#define PWM_ENABLE_PWM2EN       0x00000004  // PWM2 pin enable
#define PWM_ENABLE_PWM1EN       0x00000002  // PWM1 pin enable
#define PWM_ENABLE_PWM0EN       0x00000001  // PWM0 pin enable

//*****************************************************************************
//
// The following define the bit fields in the PWM Inversion register.
//
//*****************************************************************************
#define PWM_INVERT_PWM5INV      0x00000020  // PWM5 pin invert
#define PWM_INVERT_PWM4INV      0x00000010  // PWM4 pin invert
#define PWM_INVERT_PWM3INV      0x00000008  // PWM3 pin invert
#define PWM_INVERT_PWM2INV      0x00000004  // PWM2 pin invert
#define PWM_INVERT_PWM1INV      0x00000002  // PWM1 pin invert
#define PWM_INVERT_PWM0INV      0x00000001  // PWM0 pin invert

//*****************************************************************************
//
// The following define the bit fields in the PWM Fault register.
//
//*****************************************************************************
#define PWM_FAULT_FAULT5        0x00000020  // PWM5 pin fault
#define PWM_FAULT_FAULT4        0x00000010  // PWM5 pin fault
#define PWM_FAULT_FAULT3        0x00000008  // PWM5 pin fault
#define PWM_FAULT_FAULT2        0x00000004  // PWM5 pin fault
#define PWM_FAULT_FAULT1        0x00000002  // PWM5 pin fault
#define PWM_FAULT_FAULT0        0x00000001  // PWM5 pin fault

//*****************************************************************************
//
// PWM Interrupt Register bit definitions.
//
//*****************************************************************************
#define PWM_INT_INTFAULT        0x00010000  // Fault interrupt pending

//*****************************************************************************
//
// The following define the bit fields in the PWM Status register.
//
//*****************************************************************************
#define PWM_STATUS_FAULT        0x00000001  // Fault status

//*****************************************************************************
//
// PWM Generator standard offsets.
//
//*****************************************************************************
#define PWM_GEN_0_OFFSET        0x00000040  // PWM0 base
#define PWM_GEN_1_OFFSET        0x00000080  // PWM1 base
#define PWM_GEN_2_OFFSET        0x000000C0  // PWM2 base

#define PWM_O_X_CTL             0x00000000  // Gen Control Reg
#define PWM_O_X_INTEN           0x00000004  // Gen Int/Trig Enable Reg
#define PWM_O_X_RIS             0x00000008  // Gen Raw Int Status Reg
#define PWM_O_X_ISC             0x0000000C  // Gen Int Status Reg
#define PWM_O_X_LOAD            0x00000010  // Gen Load Reg
#define PWM_O_X_COUNT           0x00000014  // Gen Counter Reg
#define PWM_O_X_CMPA            0x00000018  // Gen Compare A Reg
#define PWM_O_X_CMPB            0x0000001C  // Gen Compare B Reg
#define PWM_O_X_GENA            0x00000020  // Gen Generator A Ctrl Reg
#define PWM_O_X_GENB            0x00000024  // Gen Generator B Ctrl Reg
#define PWM_O_X_DBCTL           0x00000028  // Gen Dead Band Ctrl Reg
#define PWM_O_X_DBRISE          0x0000002C  // Gen DB Rising Edge Delay Reg
#define PWM_O_X_DBFALL          0x00000030  // Gen DB Falling Edge Delay Reg

//*****************************************************************************
//
// PWM_X Control Register bit definitions.
//
//*****************************************************************************
#define PWM_X_CTL_ENABLE        0x00000001  // Master enable for gen block
#define PWM_X_CTL_MODE          0x00000002  // Counter mode, down or up/down
#define PWM_X_CTL_DEBUG         0x00000004  // Debug mode
#define PWM_X_CTL_LOADUPD       0x00000008  // Update mode for the load reg
#define PWM_X_CTL_CMPAUPD       0x00000010  // Update mode for comp A reg
#define PWM_X_CTL_CMPBUPD       0x00000020  // Update mode for comp B reg

//*****************************************************************************
//
// PWM_X Interrupt/Trigger Enable Register bit definitions.
//
//*****************************************************************************
#define PWM_X_INTEN_INTCNTZERO  0x00000001  // Int if COUNT = 0
#define PWM_X_INTEN_INTCNTLOAD  0x00000002  // Int if COUNT = LOAD
#define PWM_X_INTEN_INTCMPAU    0x00000004  // Int if COUNT = CMPA U
#define PWM_X_INTEN_INTCMPAD    0x00000008  // Int if COUNT = CMPA D
#define PWM_X_INTEN_INTCMPBU    0x00000010  // Int if COUNT = CMPA U
#define PWM_X_INTEN_INTCMPBD    0x00000020  // Int if COUNT = CMPA D
#define PWM_X_INTEN_TRCNTZERO   0x00000100  // Trig if COUNT = 0
#define PWM_X_INTEN_TRCNTLOAD   0x00000200  // Trig if COUNT = LOAD
#define PWM_X_INTEN_TRCMPAU     0x00000400  // Trig if COUNT = CMPA U
#define PWM_X_INTEN_TRCMPAD     0x00000800  // Trig if COUNT = CMPA D
#define PWM_X_INTEN_TRCMPBU     0x00001000  // Trig if COUNT = CMPA U
#define PWM_X_INTEN_TRCMPBD     0x00002000  // Trig if COUNT = CMPA D

//*****************************************************************************
//
// PWM_X Raw Interrupt Status Register bit definitions.
//
//*****************************************************************************
#define PWM_X_RIS_INTCNTZERO    0x00000001  // PWM_X_COUNT = 0 int
#define PWM_X_RIS_INTCNTLOAD    0x00000002  // PWM_X_COUNT = PWM_X_LOAD int
#define PWM_X_RIS_INTCMPAU      0x00000004  // PWM_X_COUNT = PWM_X_CMPA U int
#define PWM_X_RIS_INTCMPAD      0x00000008  // PWM_X_COUNT = PWM_X_CMPA D int
#define PWM_X_RIS_INTCMPBU      0x00000010  // PWM_X_COUNT = PWM_X_CMPB U int
#define PWM_X_RIS_INTCMPBD      0x00000020  // PWM_X_COUNT = PWM_X_CMPB D int

//*****************************************************************************
//
// PWM_X Interrupt Status Register bit definitions.
//
//*****************************************************************************
#define PWM_X_INT_INTCNTZERO    0x00000001  // PWM_X_COUNT = 0 received
#define PWM_X_INT_INTCNTLOAD    0x00000002  // PWM_X_COUNT = PWM_X_LOAD rcvd
#define PWM_X_INT_INTCMPAU      0x00000004  // PWM_X_COUNT = PWM_X_CMPA U rcvd
#define PWM_X_INT_INTCMPAD      0x00000008  // PWM_X_COUNT = PWM_X_CMPA D rcvd
#define PWM_X_INT_INTCMPBU      0x00000010  // PWM_X_COUNT = PWM_X_CMPB U rcvd
#define PWM_X_INT_INTCMPBD      0x00000020  // PWM_X_COUNT = PWM_X_CMPB D rcvd

//*****************************************************************************
//
// PWM_X Generator A/B Control Register bit definitions.
//
//*****************************************************************************
#define PWM_X_GEN_Y_ACTZERO     0x00000003  // Act PWM_X_COUNT = 0
#define PWM_X_GEN_Y_ACTLOAD     0x0000000C  // Act PWM_X_COUNT = PWM_X_LOAD
#define PWM_X_GEN_Y_ACTCMPAU    0x00000030  // Act PWM_X_COUNT = PWM_X_CMPA U
#define PWM_X_GEN_Y_ACTCMPAD    0x000000C0  // Act PWM_X_COUNT = PWM_X_CMPA D
#define PWM_X_GEN_Y_ACTCMPBU    0x00000300  // Act PWM_X_COUNT = PWM_X_CMPB U
#define PWM_X_GEN_Y_ACTCMPBD    0x00000C00  // Act PWM_X_COUNT = PWM_X_CMPB D

//*****************************************************************************
//
// PWM_X Generator A/B Control Register action definitions.
//
//*****************************************************************************
#define PWM_GEN_ACT_NONE        0x0         // Do nothing
#define PWM_GEN_ACT_INV         0x1         // Invert the output signal
#define PWM_GEN_ACT_ZERO        0x2         // Set the output signal to zero
#define PWM_GEN_ACT_ONE         0x3         // Set the output signal to one
#define PWM_GEN_ACT_ZERO_SHIFT  0           // Shift amount for the zero action
#define PWM_GEN_ACT_LOAD_SHIFT  2           // Shift amount for the load action
#define PWM_GEN_ACT_A_UP_SHIFT  4           // Shift amount for the A up action
#define PWM_GEN_ACT_A_DN_SHIFT  6           // Shift amount for the A dn action
#define PWM_GEN_ACT_B_UP_SHIFT  8           // Shift amount for the B up action
#define PWM_GEN_ACT_B_DN_SHIFT  10          // Shift amount for the B dn action

//*****************************************************************************
//
// PWM_X Dead Band Control Register bit definitions.
//
//*****************************************************************************
#define PWM_DBCTL_ENABLE        0x00000001  // Enable dead band insertion

//*****************************************************************************
//
// PWM Register reset values.
//
//*****************************************************************************
#define PWM_RV_CTL              0x00000000  // Master control of the PWM module
#define PWM_RV_SYNC             0x00000000  // Counter synch for PWM generators
#define PWM_RV_ENABLE           0x00000000  // Master enable for the PWM
                                            // output pins
#define PWM_RV_INVERT           0x00000000  // Inversion control for
                                            // PWM output pins
#define PWM_RV_FAULT            0x00000000  // Fault handling for the PWM
                                            // output pins
#define PWM_RV_INTEN            0x00000000  // Interrupt enable
#define PWM_RV_RIS              0x00000000  // Raw interrupt status
#define PWM_RV_ISC              0x00000000  // Interrupt status and clearing
#define PWM_RV_STATUS           0x00000000  // Status
#define PWM_RV_X_CTL            0x00000000  // Master control of the PWM
                                            // generator block
#define PWM_RV_X_INTEN          0x00000000  // Interrupt and trigger enable
#define PWM_RV_X_RIS            0x00000000  // Raw interrupt status
#define PWM_RV_X_ISC            0x00000000  // Interrupt status and clearing
#define PWM_RV_X_LOAD           0x00000000  // The load value for the counter
#define PWM_RV_X_COUNT          0x00000000  // The current counter value
#define PWM_RV_X_CMPA           0x00000000  // The comparator A value
#define PWM_RV_X_CMPB           0x00000000  // The comparator B value
#define PWM_RV_X_GENA           0x00000000  // Controls PWM generator A
#define PWM_RV_X_GENB           0x00000000  // Controls PWM generator B
#define PWM_RV_X_DBCTL          0x00000000  // Control the dead band generator
#define PWM_RV_X_DBRISE         0x00000000  // The dead band rising edge delay
                                            // count
#define PWM_RV_X_DBFALL         0x00000000  // The dead band falling edge delay
                                            // count

#endif //  __HW_PWM_H__
