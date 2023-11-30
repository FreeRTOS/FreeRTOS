//*****************************************************************************
//
// hw_pwm.h - Defines and Macros for Pulse Width Modulation (PWM) ports
//
// Copyright (c) 2005-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __HW_PWM_H__
#define __HW_PWM_H__

//*****************************************************************************
//
// The following are defines for the PWM Module Register offsets.
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
#define PWM_O_FAULTVAL          0x00000024  // PWM Fault Condition Value
#define PWM_O_0_CTL             0x00000040  // PWM0 Control
#define PWM_O_0_INTEN           0x00000044  // PWM0 Interrupt and Trigger
                                            // Enable
#define PWM_O_0_RIS             0x00000048  // PWM0 Raw Interrupt Status
#define PWM_O_0_ISC             0x0000004C  // PWM0 Interrupt Status and Clear
#define PWM_O_0_LOAD            0x00000050  // PWM0 Load
#define PWM_O_0_COUNT           0x00000054  // PWM0 Counter
#define PWM_O_0_CMPA            0x00000058  // PWM0 Compare A
#define PWM_O_0_CMPB            0x0000005C  // PWM0 Compare B
#define PWM_O_0_GENA            0x00000060  // PWM0 Generator A Control
#define PWM_O_0_GENB            0x00000064  // PWM0 Generator B Control
#define PWM_O_0_DBCTL           0x00000068  // PWM0 Dead-Band Control
#define PWM_O_0_DBRISE          0x0000006C  // PWM0 Dead-Band Rising-Edge Delay
#define PWM_O_0_DBFALL          0x00000070  // PWM0 Dead-Band
                                            // Falling-Edge-Delay
#define PWM_O_0_FLTSRC0         0x00000074  // PWM0 Fault Source 0
#define PWM_O_0_MINFLTPER       0x0000007C  // PWM0 Minimum Fault Period
#define PWM_O_1_CTL             0x00000080  // PWM1 Control
#define PWM_O_1_INTEN           0x00000084  // PWM1 Interrupt Enable
#define PWM_O_1_RIS             0x00000088  // PWM1 Raw Interrupt Status
#define PWM_O_1_ISC             0x0000008C  // PWM1 Interrupt Status and Clear
#define PWM_O_1_LOAD            0x00000090  // PWM1 Load
#define PWM_O_1_COUNT           0x00000094  // PWM1 Counter
#define PWM_O_1_CMPA            0x00000098  // PWM1 Compare A
#define PWM_O_1_CMPB            0x0000009C  // PWM1 Compare B
#define PWM_O_1_GENA            0x000000A0  // PWM1 Generator A Control
#define PWM_O_1_GENB            0x000000A4  // PWM1 Generator B Control
#define PWM_O_1_DBCTL           0x000000A8  // PWM1 Dead-Band Control
#define PWM_O_1_DBRISE          0x000000AC  // PWM1 Dead-Band Rising-Edge Delay
#define PWM_O_1_DBFALL          0x000000B0  // PWM1 Dead-Band
                                            // Falling-Edge-Delay
#define PWM_O_1_FLTSRC0         0x000000B4  // PWM1 Fault Source 0
#define PWM_O_1_MINFLTPER       0x000000BC  // PWM1 Minimum Fault Period
#define PWM_O_2_CTL             0x000000C0  // PWM2 Control
#define PWM_O_2_INTEN           0x000000C4  // PWM2 InterruptEnable
#define PWM_O_2_RIS             0x000000C8  // PWM2 Raw Interrupt Status
#define PWM_O_2_ISC             0x000000CC  // PWM2 Interrupt Status and Clear
#define PWM_O_2_LOAD            0x000000D0  // PWM2 Load
#define PWM_O_2_COUNT           0x000000D4  // PWM2 Counter
#define PWM_O_2_CMPA            0x000000D8  // PWM2 Compare A
#define PWM_O_2_CMPB            0x000000DC  // PWM2 Compare B
#define PWM_O_2_GENA            0x000000E0  // PWM2 Generator A Control
#define PWM_O_2_GENB            0x000000E4  // PWM2 Generator B Control
#define PWM_O_2_DBCTL           0x000000E8  // PWM2 Dead-Band Control
#define PWM_O_2_DBRISE          0x000000EC  // PWM2 Dead-Band Rising-Edge Delay
#define PWM_O_2_DBFALL          0x000000F0  // PWM2 Dead-Band
                                            // Falling-Edge-Delay
#define PWM_O_2_FLTSRC0         0x000000F4  // PWM2 Fault Source 0
#define PWM_O_2_MINFLTPER       0x000000FC  // PWM2 Minimum Fault Period
#define PWM_O_3_CTL             0x00000100  // PWM3 Control
#define PWM_O_3_INTEN           0x00000104  // PWM3 Interrupt and Trigger
                                            // Enable
#define PWM_O_3_RIS             0x00000108  // PWM3 Raw Interrupt Status
#define PWM_O_3_ISC             0x0000010C  // PWM3 Interrupt Status and Clear
#define PWM_O_3_LOAD            0x00000110  // PWM3 Load
#define PWM_O_3_COUNT           0x00000114  // PWM3 Counter
#define PWM_O_3_CMPA            0x00000118  // PWM3 Compare A
#define PWM_O_3_CMPB            0x0000011C  // PWM3 Compare B
#define PWM_O_3_GENA            0x00000120  // PWM3 Generator A Control
#define PWM_O_3_GENB            0x00000124  // PWM3 Generator B Control
#define PWM_O_3_DBCTL           0x00000128  // PWM3 Dead-Band Control
#define PWM_O_3_DBRISE          0x0000012C  // PWM3 Dead-Band Rising-Edge Delay
#define PWM_O_3_DBFALL          0x00000130  // PWM3 Dead-Band
                                            // Falling-Edge-Delay
#define PWM_O_3_FLTSRC0         0x00000134  // PWM3 Fault Source 0
#define PWM_O_3_MINFLTPER       0x0000013C  // PWM3 Minimum Fault Period
#define PWM_O_0_FLTSEN          0x00000800  // PWM0 Fault Pin Logic Sense
#define PWM_O_0_FLTSTAT0        0x00000804  // PWM0 Fault Status 0
#define PWM_O_1_FLTSEN          0x00000880  // PWM1 Fault Pin Logic Sense
#define PWM_O_1_FLTSTAT0        0x00000884  // PWM1 Fault Status 0
#define PWM_O_2_FLTSEN          0x00000900  // PWM2 Fault Pin Logic Sense
#define PWM_O_2_FLTSTAT0        0x00000904  // PWM2 Fault Status 0
#define PWM_O_3_FLTSEN          0x00000980  // PWM3 Fault Pin Logic Sense
#define PWM_O_3_FLTSTAT0        0x00000984  // PWM3 Fault Status 0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM Master Control
// register.
//
//*****************************************************************************
#define PWM_CTL_GLOBALSYNC3     0x00000008  // Update PWM Generator 3.
#define PWM_CTL_GLOBALSYNC2     0x00000004  // Update PWM Generator 2.
#define PWM_CTL_GLOBALSYNC1     0x00000002  // Update PWM Generator 1.
#define PWM_CTL_GLOBALSYNC0     0x00000001  // Update PWM Generator 0.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM Time Base Sync
// register.
//
//*****************************************************************************
#define PWM_SYNC_SYNC3          0x00000008  // Reset generator 3 counter
#define PWM_SYNC_SYNC2          0x00000004  // Reset generator 2 counter
#define PWM_SYNC_SYNC1          0x00000002  // Reset generator 1 counter
#define PWM_SYNC_SYNC0          0x00000001  // Reset generator 0 counter

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM Output Enable
// register.
//
//*****************************************************************************
#define PWM_ENABLE_PWM7EN       0x00000080  // PWM7 pin enable
#define PWM_ENABLE_PWM6EN       0x00000040  // PWM6 pin enable
#define PWM_ENABLE_PWM5EN       0x00000020  // PWM5 pin enable
#define PWM_ENABLE_PWM4EN       0x00000010  // PWM4 pin enable
#define PWM_ENABLE_PWM3EN       0x00000008  // PWM3 pin enable
#define PWM_ENABLE_PWM2EN       0x00000004  // PWM2 pin enable
#define PWM_ENABLE_PWM1EN       0x00000002  // PWM1 pin enable
#define PWM_ENABLE_PWM0EN       0x00000001  // PWM0 pin enable

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM Inversion register.
//
//*****************************************************************************
#define PWM_INVERT_PWM7INV      0x00000080  // PWM7 pin invert
#define PWM_INVERT_PWM6INV      0x00000040  // PWM6 pin invert
#define PWM_INVERT_PWM5INV      0x00000020  // PWM5 pin invert
#define PWM_INVERT_PWM4INV      0x00000010  // PWM4 pin invert
#define PWM_INVERT_PWM3INV      0x00000008  // PWM3 pin invert
#define PWM_INVERT_PWM2INV      0x00000004  // PWM2 pin invert
#define PWM_INVERT_PWM1INV      0x00000002  // PWM1 pin invert
#define PWM_INVERT_PWM0INV      0x00000001  // PWM0 pin invert

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM Fault register.
//
//*****************************************************************************
#define PWM_FAULT_FAULT7        0x00000080  // PWM7 pin fault
#define PWM_FAULT_FAULT6        0x00000040  // PWM6 pin fault
#define PWM_FAULT_FAULT5        0x00000020  // PWM5 pin fault
#define PWM_FAULT_FAULT4        0x00000010  // PWM4 pin fault
#define PWM_FAULT_FAULT3        0x00000008  // PWM3 pin fault
#define PWM_FAULT_FAULT2        0x00000004  // PWM2 pin fault
#define PWM_FAULT_FAULT1        0x00000002  // PWM1 pin fault
#define PWM_FAULT_FAULT0        0x00000001  // PWM0 pin fault

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM Status register.
//
//*****************************************************************************
#define PWM_STATUS_FAULT3       0x00000008  // Fault3 Interrupt Status.
#define PWM_STATUS_FAULT2       0x00000004  // Fault2 Interrupt Status.
#define PWM_STATUS_FAULT1       0x00000002  // Fault1 Interrupt Status.
#define PWM_STATUS_FAULT0       0x00000001  // Fault0 Interrupt Status.

//*****************************************************************************
//
// The following are defines for the PWM Generator standard offsets.
//
//*****************************************************************************
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
#define PWM_O_X_FLTSRC0         0x00000034  // Fault pin, comparator condition
#define PWM_O_X_MINFLTPER       0x0000003C  // Fault minimum period extension
#define PWM_GEN_0_OFFSET        0x00000040  // PWM0 base
#define PWM_GEN_1_OFFSET        0x00000080  // PWM1 base
#define PWM_GEN_2_OFFSET        0x000000C0  // PWM2 base
#define PWM_GEN_3_OFFSET        0x00000100  // PWM3 base

//*****************************************************************************
//
// The following are defines for the PWM_X Control Register bit definitions.
//
//*****************************************************************************
#define PWM_X_CTL_LATCH         0x00040000  // Latch Fault Input.
#define PWM_X_CTL_MINFLTPER     0x00020000  // Minimum fault period enabled
#define PWM_X_CTL_FLTSRC        0x00010000  // Fault Condition Source.
#define PWM_X_CTL_DBFALLUPD_M   0x0000C000  // Specifies the update mode for
                                            // the PWMnDBFALL register.
#define PWM_X_CTL_DBFALLUPD_I   0x00000000  // Immediate
#define PWM_X_CTL_DBFALLUPD_LS  0x00008000  // Locally Synchronized
#define PWM_X_CTL_DBFALLUPD_GS  0x0000C000  // Globally Synchronized
#define PWM_X_CTL_DBRISEUPD_M   0x00003000  // PWMnDBRISE Update Mode.
#define PWM_X_CTL_DBRISEUPD_I   0x00000000  // Immediate
#define PWM_X_CTL_DBRISEUPD_LS  0x00002000  // Locally Synchronized
#define PWM_X_CTL_DBRISEUPD_GS  0x00003000  // Globally Synchronized
#define PWM_X_CTL_DBCTLUPD_M    0x00000C00  // PWMnDBCTL Update Mode.
#define PWM_X_CTL_DBCTLUPD_I    0x00000000  // Immediate
#define PWM_X_CTL_DBCTLUPD_LS   0x00000800  // Locally Synchronized
#define PWM_X_CTL_DBCTLUPD_GS   0x00000C00  // Globally Synchronized
#define PWM_X_CTL_GENBUPD_M     0x00000300  // PWMnGENB Update Mode.
#define PWM_X_CTL_GENBUPD_I     0x00000000  // Immediate
#define PWM_X_CTL_GENBUPD_LS    0x00000200  // Locally Synchronized
#define PWM_X_CTL_GENBUPD_GS    0x00000300  // Globally Synchronized
#define PWM_X_CTL_GENAUPD_M     0x000000C0  // PWMnGENA Update Mode.
#define PWM_X_CTL_GENAUPD_I     0x00000000  // Immediate
#define PWM_X_CTL_GENAUPD_LS    0x00000080  // Locally Synchronized
#define PWM_X_CTL_GENAUPD_GS    0x000000C0  // Globally Synchronized
#define PWM_X_CTL_CMPBUPD       0x00000020  // Update mode for comp B reg
#define PWM_X_CTL_CMPAUPD       0x00000010  // Update mode for comp A reg
#define PWM_X_CTL_LOADUPD       0x00000008  // Update mode for the load reg
#define PWM_X_CTL_DEBUG         0x00000004  // Debug mode
#define PWM_X_CTL_MODE          0x00000002  // Counter mode, down or up/down
#define PWM_X_CTL_ENABLE        0x00000001  // Master enable for gen block

//*****************************************************************************
//
// The following are defines for the PWM Generator extended offsets.
//
//*****************************************************************************
#define PWM_O_X_FLTSEN          0x00000000  // Fault logic sense
#define PWM_O_X_FLTSTAT0        0x00000004  // Pin and comparator status
#define PWM_EXT_0_OFFSET        0x00000800  // PWM0 extended base
#define PWM_EXT_1_OFFSET        0x00000880  // PWM1 extended base
#define PWM_EXT_2_OFFSET        0x00000900  // PWM2 extended base
#define PWM_EXT_3_OFFSET        0x00000980  // PWM3 extended base

//*****************************************************************************
//
// The following are defines for the PWM_X Interrupt/Trigger Enable Register
// bit definitions.
//
//*****************************************************************************
#define PWM_X_INTEN_TRCMPBD     0x00002000  // Trig if COUNT = CMPA D
#define PWM_X_INTEN_TRCMPBU     0x00001000  // Trig if COUNT = CMPA U
#define PWM_X_INTEN_TRCMPAD     0x00000800  // Trig if COUNT = CMPA D
#define PWM_X_INTEN_TRCMPAU     0x00000400  // Trig if COUNT = CMPA U
#define PWM_X_INTEN_TRCNTLOAD   0x00000200  // Trig if COUNT = LOAD
#define PWM_X_INTEN_TRCNTZERO   0x00000100  // Trig if COUNT = 0
#define PWM_X_INTEN_INTCMPBD    0x00000020  // Int if COUNT = CMPA D
#define PWM_X_INTEN_INTCMPBU    0x00000010  // Int if COUNT = CMPA U
#define PWM_X_INTEN_INTCMPAD    0x00000008  // Int if COUNT = CMPA D
#define PWM_X_INTEN_INTCMPAU    0x00000004  // Int if COUNT = CMPA U
#define PWM_X_INTEN_INTCNTLOAD  0x00000002  // Int if COUNT = LOAD
#define PWM_X_INTEN_INTCNTZERO  0x00000001  // Int if COUNT = 0

//*****************************************************************************
//
// The following are defines for the PWM_X Raw Interrupt Status Register bit
// definitions.
//
//*****************************************************************************
#define PWM_X_RIS_INTCMPBD      0x00000020  // PWM_X_COUNT = PWM_X_CMPB D int
#define PWM_X_RIS_INTCMPBU      0x00000010  // PWM_X_COUNT = PWM_X_CMPB U int
#define PWM_X_RIS_INTCMPAD      0x00000008  // PWM_X_COUNT = PWM_X_CMPA D int
#define PWM_X_RIS_INTCMPAU      0x00000004  // PWM_X_COUNT = PWM_X_CMPA U int
#define PWM_X_RIS_INTCNTLOAD    0x00000002  // PWM_X_COUNT = PWM_X_LOAD int
#define PWM_X_RIS_INTCNTZERO    0x00000001  // PWM_X_COUNT = 0 int

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_INTEN register.
//
//*****************************************************************************
#define PWM_INTEN_INTFAULT3     0x00080000  // Interrupt Fault 3.
#define PWM_INTEN_INTFAULT2     0x00040000  // Interrupt Fault 2.
#define PWM_INTEN_INTFAULT1     0x00020000  // Interrupt Fault 1.
#define PWM_INTEN_INTFAULT      0x00010000  // Fault Interrupt Enable.
#define PWM_INTEN_INTFAULT0     0x00010000  // Interrupt Fault 0.
#define PWM_INTEN_INTPWM3       0x00000008  // PWM3 Interrupt Enable.
#define PWM_INTEN_INTPWM2       0x00000004  // PWM2 Interrupt Enable.
#define PWM_INTEN_INTPWM1       0x00000002  // PWM1 Interrupt Enable.
#define PWM_INTEN_INTPWM0       0x00000001  // PWM0 Interrupt Enable.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_RIS register.
//
//*****************************************************************************
#define PWM_RIS_INTFAULT3       0x00080000  // Interrupt Fault PWM 3.
#define PWM_RIS_INTFAULT2       0x00040000  // Interrupt Fault PWM 2.
#define PWM_RIS_INTFAULT1       0x00020000  // Interrupt Fault PWM 1.
#define PWM_RIS_INTFAULT0       0x00010000  // Interrupt Fault PWM 0.
#define PWM_RIS_INTFAULT        0x00010000  // Fault Interrupt Asserted.
#define PWM_RIS_INTPWM3         0x00000008  // PWM3 Interrupt Asserted.
#define PWM_RIS_INTPWM2         0x00000004  // PWM2 Interrupt Asserted.
#define PWM_RIS_INTPWM1         0x00000002  // PWM1 Interrupt Asserted.
#define PWM_RIS_INTPWM0         0x00000001  // PWM0 Interrupt Asserted.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_ISC register.
//
//*****************************************************************************
#define PWM_ISC_INTFAULT3       0x00080000  // FAULT3 Interrupt Asserted.
#define PWM_ISC_INTFAULT2       0x00040000  // FAULT2 Interrupt Asserted.
#define PWM_ISC_INTFAULT1       0x00020000  // FAULT1 Interrupt Asserted.
#define PWM_ISC_INTFAULT        0x00010000  // Fault Interrupt Asserted.
#define PWM_ISC_INTFAULT0       0x00010000  // FAULT0 Interrupt Asserted.
#define PWM_ISC_INTPWM3         0x00000008  // PWM3 Interrupt Status.
#define PWM_ISC_INTPWM2         0x00000004  // PWM2 Interrupt Status.
#define PWM_ISC_INTPWM1         0x00000002  // PWM1 Interrupt Status.
#define PWM_ISC_INTPWM0         0x00000001  // PWM0 Interrupt Status.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_ISC register.
//
//*****************************************************************************
#define PWM_X_ISC_INTCMPBD      0x00000020  // Comparator B Down Interrupt.
#define PWM_X_ISC_INTCMPBU      0x00000010  // Comparator B Up Interrupt.
#define PWM_X_ISC_INTCMPAD      0x00000008  // Comparator A Down Interrupt.
#define PWM_X_ISC_INTCMPAU      0x00000004  // Comparator A Up Interrupt.
#define PWM_X_ISC_INTCNTLOAD    0x00000002  // Counter=Load Interrupt.
#define PWM_X_ISC_INTCNTZERO    0x00000001  // Counter=0 Interrupt.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_LOAD register.
//
//*****************************************************************************
#define PWM_X_LOAD_M            0x0000FFFF  // Counter Load Value.
#define PWM_X_LOAD_S            0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_COUNT register.
//
//*****************************************************************************
#define PWM_X_COUNT_M           0x0000FFFF  // Counter Value.
#define PWM_X_COUNT_S           0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_CMPA register.
//
//*****************************************************************************
#define PWM_X_CMPA_M            0x0000FFFF  // Comparator A Value.
#define PWM_X_CMPA_S            0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_CMPB register.
//
//*****************************************************************************
#define PWM_X_CMPB_M            0x0000FFFF  // Comparator B Value.
#define PWM_X_CMPB_S            0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_GENA register.
//
//*****************************************************************************
#define PWM_X_GENA_ACTCMPBD_M   0x00000C00  // Action for Comparator B Down.
#define PWM_X_GENA_ACTCMPBD_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENA_ACTCMPBD_INV 0x00000400  // Invert the output signal.
#define PWM_X_GENA_ACTCMPBD_ZERO \
                                0x00000800  // Set the output signal to 0.
#define PWM_X_GENA_ACTCMPBD_ONE 0x00000C00  // Set the output signal to 1.
#define PWM_X_GENA_ACTCMPBU_M   0x00000300  // Action for Comparator B Up.
#define PWM_X_GENA_ACTCMPBU_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENA_ACTCMPBU_INV 0x00000100  // Invert the output signal.
#define PWM_X_GENA_ACTCMPBU_ZERO \
                                0x00000200  // Set the output signal to 0.
#define PWM_X_GENA_ACTCMPBU_ONE 0x00000300  // Set the output signal to 1.
#define PWM_X_GENA_ACTCMPAD_M   0x000000C0  // Action for Comparator A Down.
#define PWM_X_GENA_ACTCMPAD_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENA_ACTCMPAD_INV 0x00000040  // Invert the output signal.
#define PWM_X_GENA_ACTCMPAD_ZERO \
                                0x00000080  // Set the output signal to 0.
#define PWM_X_GENA_ACTCMPAD_ONE 0x000000C0  // Set the output signal to 1.
#define PWM_X_GENA_ACTCMPAU_M   0x00000030  // Action for Comparator A Up.
#define PWM_X_GENA_ACTCMPAU_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENA_ACTCMPAU_INV 0x00000010  // Invert the output signal.
#define PWM_X_GENA_ACTCMPAU_ZERO \
                                0x00000020  // Set the output signal to 0.
#define PWM_X_GENA_ACTCMPAU_ONE 0x00000030  // Set the output signal to 1.
#define PWM_X_GENA_ACTLOAD_M    0x0000000C  // Action for Counter=Load.
#define PWM_X_GENA_ACTLOAD_NONE 0x00000000  // Do nothing.
#define PWM_X_GENA_ACTLOAD_INV  0x00000004  // Invert the output signal.
#define PWM_X_GENA_ACTLOAD_ZERO 0x00000008  // Set the output signal to 0.
#define PWM_X_GENA_ACTLOAD_ONE  0x0000000C  // Set the output signal to 1.
#define PWM_X_GENA_ACTZERO_M    0x00000003  // Action for Counter=0.
#define PWM_X_GENA_ACTZERO_NONE 0x00000000  // Do nothing.
#define PWM_X_GENA_ACTZERO_INV  0x00000001  // Invert the output signal.
#define PWM_X_GENA_ACTZERO_ZERO 0x00000002  // Set the output signal to 0.
#define PWM_X_GENA_ACTZERO_ONE  0x00000003  // Set the output signal to 1.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_GENB register.
//
//*****************************************************************************
#define PWM_X_GENB_ACTCMPBD_M   0x00000C00  // Action for Comparator B Down.
#define PWM_X_GENB_ACTCMPBD_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENB_ACTCMPBD_INV 0x00000400  // Invert the output signal.
#define PWM_X_GENB_ACTCMPBD_ZERO \
                                0x00000800  // Set the output signal to 0.
#define PWM_X_GENB_ACTCMPBD_ONE 0x00000C00  // Set the output signal to 1.
#define PWM_X_GENB_ACTCMPBU_M   0x00000300  // Action for Comparator B Up.
#define PWM_X_GENB_ACTCMPBU_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENB_ACTCMPBU_INV 0x00000100  // Invert the output signal.
#define PWM_X_GENB_ACTCMPBU_ZERO \
                                0x00000200  // Set the output signal to 0.
#define PWM_X_GENB_ACTCMPBU_ONE 0x00000300  // Set the output signal to 1.
#define PWM_X_GENB_ACTCMPAD_M   0x000000C0  // Action for Comparator A Down.
#define PWM_X_GENB_ACTCMPAD_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENB_ACTCMPAD_INV 0x00000040  // Invert the output signal.
#define PWM_X_GENB_ACTCMPAD_ZERO \
                                0x00000080  // Set the output signal to 0.
#define PWM_X_GENB_ACTCMPAD_ONE 0x000000C0  // Set the output signal to 1.
#define PWM_X_GENB_ACTCMPAU_M   0x00000030  // Action for Comparator A Up.
#define PWM_X_GENB_ACTCMPAU_NONE \
                                0x00000000  // Do nothing.
#define PWM_X_GENB_ACTCMPAU_INV 0x00000010  // Invert the output signal.
#define PWM_X_GENB_ACTCMPAU_ZERO \
                                0x00000020  // Set the output signal to 0.
#define PWM_X_GENB_ACTCMPAU_ONE 0x00000030  // Set the output signal to 1.
#define PWM_X_GENB_ACTLOAD_M    0x0000000C  // Action for Counter=Load.
#define PWM_X_GENB_ACTLOAD_NONE 0x00000000  // Do nothing.
#define PWM_X_GENB_ACTLOAD_INV  0x00000004  // Invert the output signal.
#define PWM_X_GENB_ACTLOAD_ZERO 0x00000008  // Set the output signal to 0.
#define PWM_X_GENB_ACTLOAD_ONE  0x0000000C  // Set the output signal to 1.
#define PWM_X_GENB_ACTZERO_M    0x00000003  // Action for Counter=0.
#define PWM_X_GENB_ACTZERO_NONE 0x00000000  // Do nothing.
#define PWM_X_GENB_ACTZERO_INV  0x00000001  // Invert the output signal.
#define PWM_X_GENB_ACTZERO_ZERO 0x00000002  // Set the output signal to 0.
#define PWM_X_GENB_ACTZERO_ONE  0x00000003  // Set the output signal to 1.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_DBCTL register.
//
//*****************************************************************************
#define PWM_X_DBCTL_ENABLE      0x00000001  // Dead-Band Generator Enable.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_DBRISE register.
//
//*****************************************************************************
#define PWM_X_DBRISE_DELAY_M    0x00000FFF  // Dead-Band Rise Delay.
#define PWM_X_DBRISE_DELAY_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_DBFALL register.
//
//*****************************************************************************
#define PWM_X_DBFALL_DELAY_M    0x00000FFF  // Dead-Band Fall Delay.
#define PWM_X_DBFALL_DELAY_S    0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_FAULTVAL register.
//
//*****************************************************************************
#define PWM_FAULTVAL_PWM7       0x00000080  // PWM7 Fault Value.
#define PWM_FAULTVAL_PWM6       0x00000040  // PWM6 Fault Value.
#define PWM_FAULTVAL_PWM5       0x00000020  // PWM5 Fault Value.
#define PWM_FAULTVAL_PWM4       0x00000010  // PWM4 Fault Value.
#define PWM_FAULTVAL_PWM3       0x00000008  // PWM3 Fault Value.
#define PWM_FAULTVAL_PWM2       0x00000004  // PWM2 Fault Value.
#define PWM_FAULTVAL_PWM1       0x00000002  // PWM1 Fault Value.
#define PWM_FAULTVAL_PWM0       0x00000001  // PWM0 Fault Value.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_MINFLTPER
// register.
//
//*****************************************************************************
#define PWM_X_MINFLTPER_M       0x0000FFFF  // Minimum Fault Period.
#define PWM_X_MINFLTPER_S       0

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_FLTSEN register.
//
//*****************************************************************************
#define PWM_X_FLTSEN_FAULT3     0x00000008  // Fault3 Sense.
#define PWM_X_FLTSEN_FAULT2     0x00000004  // Fault2 Sense.
#define PWM_X_FLTSEN_FAULT1     0x00000002  // Fault1 Sense.
#define PWM_X_FLTSEN_FAULT0     0x00000001  // Fault0 Sense.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_FLTSRC0
// register.
//
//*****************************************************************************
#define PWM_X_FLTSRC0_FAULT3    0x00000008  // Fault3.
#define PWM_X_FLTSRC0_FAULT2    0x00000004  // Fault2.
#define PWM_X_FLTSRC0_FAULT1    0x00000002  // Fault1.
#define PWM_X_FLTSRC0_FAULT0    0x00000001  // Fault0.

//*****************************************************************************
//
// The following are defines for the bit fields in the PWM_O_X_FLTSTAT0
// register.
//
//*****************************************************************************
#define PWM_X_FLTSTAT0_FAULT3   0x00000008  // Fault Input 3.
#define PWM_X_FLTSTAT0_FAULT2   0x00000004  // Fault Input 2.
#define PWM_X_FLTSTAT0_FAULT1   0x00000002  // Fault Input 1.
#define PWM_X_FLTSTAT0_FAULT0   0x00000001  // Fault Input 0.

//*****************************************************************************
//
// The following definitions are deprecated.
//
//*****************************************************************************
#ifndef DEPRECATED

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the PWM Master
// Control register.
//
//*****************************************************************************
#define PWM_CTL_GLOBAL_SYNC2    0x00000004  // Global sync generator 2
#define PWM_CTL_GLOBAL_SYNC1    0x00000002  // Global sync generator 1
#define PWM_CTL_GLOBAL_SYNC0    0x00000001  // Global sync generator 0

//*****************************************************************************
//
// The following are deprecated defines for the PWM Interrupt Register bit
// definitions.
//
//*****************************************************************************
#define PWM_INT_INTFAULT        0x00010000  // Fault interrupt pending

//*****************************************************************************
//
// The following are deprecated defines for the bit fields in the PWM Status
// register.
//
//*****************************************************************************
#define PWM_STATUS_FAULT        0x00000001  // Fault status

//*****************************************************************************
//
// The following are deprecated defines for the PWM_X Interrupt Status Register
// bit definitions.
//
//*****************************************************************************
#define PWM_X_INT_INTCMPBD      0x00000020  // PWM_X_COUNT = PWM_X_CMPB D rcvd
#define PWM_X_INT_INTCMPBU      0x00000010  // PWM_X_COUNT = PWM_X_CMPB U rcvd
#define PWM_X_INT_INTCMPAD      0x00000008  // PWM_X_COUNT = PWM_X_CMPA D rcvd
#define PWM_X_INT_INTCMPAU      0x00000004  // PWM_X_COUNT = PWM_X_CMPA U rcvd
#define PWM_X_INT_INTCNTLOAD    0x00000002  // PWM_X_COUNT = PWM_X_LOAD rcvd
#define PWM_X_INT_INTCNTZERO    0x00000001  // PWM_X_COUNT = 0 received

//*****************************************************************************
//
// The following are deprecated defines for the PWM_X Generator A/B Control
// Register bit definitions.
//
//*****************************************************************************
#define PWM_X_GEN_Y_ACTCMPBD    0x00000C00  // Act PWM_X_COUNT = PWM_X_CMPB D
#define PWM_X_GEN_Y_ACTCMPBU    0x00000300  // Act PWM_X_COUNT = PWM_X_CMPB U
#define PWM_X_GEN_Y_ACTCMPAD    0x000000C0  // Act PWM_X_COUNT = PWM_X_CMPA D
#define PWM_X_GEN_Y_ACTCMPAU    0x00000030  // Act PWM_X_COUNT = PWM_X_CMPA U
#define PWM_X_GEN_Y_ACTLOAD     0x0000000C  // Act PWM_X_COUNT = PWM_X_LOAD
#define PWM_X_GEN_Y_ACTZERO     0x00000003  // Act PWM_X_COUNT = 0

//*****************************************************************************
//
// The following are deprecated defines for the PWM_X Generator A/B Control
// Register action definitions.
//
//*****************************************************************************
#define PWM_GEN_ACT_ONE         0x00000003  // Set the output signal to one
#define PWM_GEN_ACT_ZERO        0x00000002  // Set the output signal to zero
#define PWM_GEN_ACT_INV         0x00000001  // Invert the output signal
#define PWM_GEN_ACT_NONE        0x00000000  // Do nothing
#define PWM_GEN_ACT_B_DN_SHIFT  10          // Shift amount for the B dn action
#define PWM_GEN_ACT_B_UP_SHIFT  8           // Shift amount for the B up action
#define PWM_GEN_ACT_A_DN_SHIFT  6           // Shift amount for the A dn action
#define PWM_GEN_ACT_A_UP_SHIFT  4           // Shift amount for the A up action
#define PWM_GEN_ACT_LOAD_SHIFT  2           // Shift amount for the load action
#define PWM_GEN_ACT_ZERO_SHIFT  0           // Shift amount for the zero action

//*****************************************************************************
//
// The following are deprecated defines for the PWM_X Dead Band Control
// Register bit definitions.
//
//*****************************************************************************
#define PWM_DBCTL_ENABLE        0x00000001  // Enable dead band insertion

//*****************************************************************************
//
// The following are deprecated defines for the PWM Register reset values.
//
//*****************************************************************************
#define PWM_RV_X_DBCTL          0x00000000  // Control the dead band generator
#define PWM_RV_STATUS           0x00000000  // Status
#define PWM_RV_X_ISC            0x00000000  // Interrupt status and clearing
#define PWM_RV_X_RIS            0x00000000  // Raw interrupt status
#define PWM_RV_X_CTL            0x00000000  // Master control of the PWM
                                            // generator block
#define PWM_RV_SYNC             0x00000000  // Counter synch for PWM generators
#define PWM_RV_X_DBFALL         0x00000000  // The dead band falling edge delay
                                            // count
#define PWM_RV_X_INTEN          0x00000000  // Interrupt and trigger enable
#define PWM_RV_X_LOAD           0x00000000  // The load value for the counter
#define PWM_RV_X_GENA           0x00000000  // Controls PWM generator A
#define PWM_RV_CTL              0x00000000  // Master control of the PWM module
#define PWM_RV_FAULT            0x00000000  // Fault handling for the PWM
                                            // output pins
#define PWM_RV_RIS              0x00000000  // Raw interrupt status
#define PWM_RV_X_CMPA           0x00000000  // The comparator A value
#define PWM_RV_INVERT           0x00000000  // Inversion control for PWM output
                                            // pins
#define PWM_RV_X_DBRISE         0x00000000  // The dead band rising edge delay
                                            // count
#define PWM_RV_ENABLE           0x00000000  // Master enable for the PWM output
                                            // pins
#define PWM_RV_X_GENB           0x00000000  // Controls PWM generator B
#define PWM_RV_X_CMPB           0x00000000  // The comparator B value
#define PWM_RV_ISC              0x00000000  // Interrupt status and clearing
#define PWM_RV_INTEN            0x00000000  // Interrupt enable
#define PWM_RV_X_COUNT          0x00000000  // The current counter value

#endif

#endif // __HW_PWM_H__
