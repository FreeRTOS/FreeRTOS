//*****************************************************************************
//
// comp.h - Prototypes for the analog comparator driver.
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

#ifndef __COMP_H__
#define __COMP_H__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Values that can be passed to ComparatorConfigure() as the ulConfig
// parameter.  For each group (i.e. COMP_TRIG_xxx, COMP_INT_xxx, etc.), one of
// the values may be selected and combined together with values from the other
// groups via a logical OR.
//
//*****************************************************************************
#define COMP_TRIG_NONE          0x00000000  // No ADC trigger
#define COMP_TRIG_HIGH          0x00000880  // Trigger when high
#define COMP_TRIG_LOW           0x00000800  // Trigger when low
#define COMP_TRIG_FALL          0x00000820  // Trigger on falling edge
#define COMP_TRIG_RISE          0x00000840  // Trigger on rising edge
#define COMP_TRIG_BOTH          0x00000860  // Trigger on both edges
#define COMP_INT_HIGH           0x00000010  // Interrupt when high
#define COMP_INT_LOW            0x00000000  // Interrupt when low
#define COMP_INT_FALL           0x00000004  // Interrupt on falling edge
#define COMP_INT_RISE           0x00000008  // Interrupt on rising edge
#define COMP_INT_BOTH           0x0000000C  // Interrupt on both edges
#define COMP_ASRCP_PIN          0x00000000  // Dedicated Comp+ pin
#define COMP_ASRCP_PIN0         0x00000200  // Comp0+ pin
#define COMP_ASRCP_REF          0x00000400  // Internal voltage reference
#ifndef DEPRECATED
#define COMP_OUTPUT_NONE        0x00000000  // No comparator output
#endif
#define COMP_OUTPUT_NORMAL      0x00000000  // Comparator output normal
#define COMP_OUTPUT_INVERT      0x00000002  // Comparator output inverted

//*****************************************************************************
//
// Values that can be passed to ComparatorSetRef() as the ulRef parameter.
//
//*****************************************************************************
#define COMP_REF_OFF            0x00000000  // Turn off the internal reference
#define COMP_REF_0V             0x00000300  // Internal reference of 0V
#define COMP_REF_0_1375V        0x00000301  // Internal reference of 0.1375V
#define COMP_REF_0_275V         0x00000302  // Internal reference of 0.275V
#define COMP_REF_0_4125V        0x00000303  // Internal reference of 0.4125V
#define COMP_REF_0_55V          0x00000304  // Internal reference of 0.55V
#define COMP_REF_0_6875V        0x00000305  // Internal reference of 0.6875V
#define COMP_REF_0_825V         0x00000306  // Internal reference of 0.825V
#define COMP_REF_0_928125V      0x00000201  // Internal reference of 0.928125V
#define COMP_REF_0_9625V        0x00000307  // Internal reference of 0.9625V
#define COMP_REF_1_03125V       0x00000202  // Internal reference of 1.03125V
#define COMP_REF_1_134375V      0x00000203  // Internal reference of 1.134375V
#define COMP_REF_1_1V           0x00000308  // Internal reference of 1.1V
#define COMP_REF_1_2375V        0x00000309  // Internal reference of 1.2375V
#define COMP_REF_1_340625V      0x00000205  // Internal reference of 1.340625V
#define COMP_REF_1_375V         0x0000030A  // Internal reference of 1.375V
#define COMP_REF_1_44375V       0x00000206  // Internal reference of 1.44375V
#define COMP_REF_1_5125V        0x0000030B  // Internal reference of 1.5125V
#define COMP_REF_1_546875V      0x00000207  // Internal reference of 1.546875V
#define COMP_REF_1_65V          0x0000030C  // Internal reference of 1.65V
#define COMP_REF_1_753125V      0x00000209  // Internal reference of 1.753125V
#define COMP_REF_1_7875V        0x0000030D  // Internal reference of 1.7875V
#define COMP_REF_1_85625V       0x0000020A  // Internal reference of 1.85625V
#define COMP_REF_1_925V         0x0000030E  // Internal reference of 1.925V
#define COMP_REF_1_959375V      0x0000020B  // Internal reference of 1.959375V
#define COMP_REF_2_0625V        0x0000030F  // Internal reference of 2.0625V
#define COMP_REF_2_165625V      0x0000020D  // Internal reference of 2.165625V
#define COMP_REF_2_26875V       0x0000020E  // Internal reference of 2.26875V
#define COMP_REF_2_371875V      0x0000020F  // Internal reference of 2.371875V

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern void ComparatorConfigure(unsigned long ulBase, unsigned long ulComp,
                                unsigned long ulConfig);
extern void ComparatorRefSet(unsigned long ulBase, unsigned long ulRef);
extern tBoolean ComparatorValueGet(unsigned long ulBase, unsigned long ulComp);
extern void ComparatorIntRegister(unsigned long ulBase, unsigned long ulComp,
                                  void (*pfnHandler)(void));
extern void ComparatorIntUnregister(unsigned long ulBase,
                                    unsigned long ulComp);
extern void ComparatorIntEnable(unsigned long ulBase, unsigned long ulComp);
extern void ComparatorIntDisable(unsigned long ulBase, unsigned long ulComp);
extern tBoolean ComparatorIntStatus(unsigned long ulBase, unsigned long ulComp,
                                    tBoolean bMasked);
extern void ComparatorIntClear(unsigned long ulBase, unsigned long ulComp);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif // __COMP_H__
