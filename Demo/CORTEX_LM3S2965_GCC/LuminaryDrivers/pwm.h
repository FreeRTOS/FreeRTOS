//*****************************************************************************
//
// pwm.h - API function protoypes for Pulse Width Modulation (PWM) ports
//
// Copyright (c) 2005-2007 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
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
// This is part of revision 1408 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __PWM_H__
#define __PWM_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// The following defines are passed to PWMGenConfigure() as the ulConfig
// parameter and specify the configuration of the PWM generator.
//
//*****************************************************************************
#define PWM_GEN_MODE_DOWN       0x00000000  // Down count mode
#define PWM_GEN_MODE_UP_DOWN    0x00000002  // Up/Down count mode
#define PWM_GEN_MODE_SYNC       0x00000038  // Synchronous updates
#define PWM_GEN_MODE_NO_SYNC    0x00000000  // Immediate updates
#define PWM_GEN_MODE_DBG_RUN    0x00000004  // Continue running in debug mode
#define PWM_GEN_MODE_DBG_STOP   0x00000000  // Stop running in debug mode

//*****************************************************************************
//
// Defines for enabling, disabling, and clearing PWM generator interrupts and
// triggers.
//
//*****************************************************************************
#define PWM_INT_CNT_ZERO        0x00000001  // Int if COUNT = 0
#define PWM_INT_CNT_LOAD        0x00000002  // Int if COUNT = LOAD
#define PWM_INT_CNT_AU          0x00000004  // Int if COUNT = CMPA U
#define PWM_INT_CNT_AD          0x00000008  // Int if COUNT = CMPA D
#define PWM_INT_CNT_BU          0x00000010  // Int if COUNT = CMPA U
#define PWM_INT_CNT_BD          0x00000020  // Int if COUNT = CMPA D
#define PWM_TR_CNT_ZERO         0x00000100  // Trig if COUNT = 0
#define PWM_TR_CNT_LOAD         0x00000200  // Trig if COUNT = LOAD
#define PWM_TR_CNT_AU           0x00000400  // Trig if COUNT = CMPA U
#define PWM_TR_CNT_AD           0x00000800  // Trig if COUNT = CMPA D
#define PWM_TR_CNT_BU           0x00001000  // Trig if COUNT = CMPA U
#define PWM_TR_CNT_BD           0x00002000  // Trig if COUNT = CMPA D

//*****************************************************************************
//
// Defines for enabling, disabling, and clearing PWM interrupts.
//
//*****************************************************************************
#define PWM_INT_GEN_0           0x00000001  // Generator 0 interrupt
#define PWM_INT_GEN_1           0x00000002  // Generator 1 interrupt
#define PWM_INT_GEN_2           0x00000004  // Generator 2 interrupt
#define PWM_INT_FAULT           0x00010000  // Fault interrupt

//*****************************************************************************
//
// Defines to identify the generators within a module.
//
//*****************************************************************************
#define PWM_GEN_0               0x00000040  // Offset address of Gen0
#define PWM_GEN_1               0x00000080  // Offset address of Gen1
#define PWM_GEN_2               0x000000C0  // Offset address of Gen2

#define PWM_GEN_0_BIT           0x00000001  // Bit-wise ID for Gen0
#define PWM_GEN_1_BIT           0x00000002  // Bit-wise ID for Gen1
#define PWM_GEN_2_BIT           0x00000004  // Bit-wise ID for Gen2

//*****************************************************************************
//
// Defines to identify the outputs within a module.
//
//*****************************************************************************
#define PWM_OUT_0               0x00000040  // Encoded offset address of PWM0
#define PWM_OUT_1               0x00000041  // Encoded offset address of PWM1
#define PWM_OUT_2               0x00000082  // Encoded offset address of PWM2
#define PWM_OUT_3               0x00000083  // Encoded offset address of PWM3
#define PWM_OUT_4               0x000000C4  // Encoded offset address of PWM4
#define PWM_OUT_5               0x000000C5  // Encoded offset address of PWM5

#define PWM_OUT_0_BIT           0x00000001  // Bit-wise ID for PWM0
#define PWM_OUT_1_BIT           0x00000002  // Bit-wise ID for PWM1
#define PWM_OUT_2_BIT           0x00000004  // Bit-wise ID for PWM2
#define PWM_OUT_3_BIT           0x00000008  // Bit-wise ID for PWM3
#define PWM_OUT_4_BIT           0x00000010  // Bit-wise ID for PWM4
#define PWM_OUT_5_BIT           0x00000020  // Bit-wise ID for PWM5

//*****************************************************************************
//
// API Function prototypes
//
//*****************************************************************************
extern void PWMGenConfigure(unsigned long ulBase, unsigned long ulGen,
                            unsigned long ulConfig);
extern void PWMGenPeriodSet(unsigned long ulBase, unsigned long ulGen,
                            unsigned long ulPeriod);
extern unsigned long PWMGenPeriodGet(unsigned long ulBase,
                                     unsigned long ulGen);
extern void PWMGenEnable(unsigned long ulBase, unsigned long ulGen);
extern void PWMGenDisable(unsigned long ulBase, unsigned long ulGen);
extern void PWMPulseWidthSet(unsigned long ulBase, unsigned long ulPWMOut,
                             unsigned long ulWidth);
extern unsigned long PWMPulseWidthGet(unsigned long ulBase,
                                      unsigned long ulPWMOut);
extern void PWMDeadBandEnable(unsigned long ulBase, unsigned long ulGen,
                              unsigned short usRise, unsigned short usFall);
extern void PWMDeadBandDisable(unsigned long ulBase, unsigned long ulGen);
extern void PWMSyncUpdate(unsigned long ulBase, unsigned long ulGenBits);
extern void PWMSyncTimeBase(unsigned long ulBase, unsigned long ulGenBits);
extern void PWMOutputState(unsigned long ulBase, unsigned long ulPWMOutBits,
                           tBoolean bEnable);
extern void PWMOutputInvert(unsigned long ulBase, unsigned long ulPWMOutBits,
                            tBoolean bInvert);
extern void PWMOutputFault(unsigned long ulBase, unsigned long ulPWMOutBits,
                           tBoolean bFaultKill);
extern void PWMGenIntRegister(unsigned long ulBase, unsigned long ulGen,
                              void (*pfnIntHandler)(void));
extern void PWMGenIntUnregister(unsigned long ulBase, unsigned long ulGen);
extern void PWMFaultIntRegister(unsigned long ulBase,
                                void (*pfnIntHandler)(void));
extern void PWMFaultIntUnregister(unsigned long ulBase);
extern void PWMGenIntTrigEnable(unsigned long ulBase, unsigned long ulGen,
                                unsigned long ulIntTrig);
extern void PWMGenIntTrigDisable(unsigned long ulBase, unsigned long ulGen,
                                 unsigned long ulIntTrig);
extern unsigned long PWMGenIntStatus(unsigned long ulBase, unsigned long ulGen,
                                     tBoolean bMasked);
extern void PWMGenIntClear(unsigned long ulBase, unsigned long ulGen,
                           unsigned long ulInts);
extern void PWMIntEnable(unsigned long ulBase, unsigned long ulGenFault);
extern void PWMIntDisable(unsigned long ulBase, unsigned long ulGenFault);
extern void PWMFaultIntClear(unsigned long ulBase);
extern unsigned long PWMIntStatus(unsigned long ulBase, tBoolean bMasked);

#ifdef __cplusplus
}
#endif

#endif // __PWM_H__
