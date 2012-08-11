//*****************************************************************************
//
// hw_comp.h - Macros used when accessing the comparator hardware.
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

#ifndef __HW_COMP_H__
#define __HW_COMP_H__

//*****************************************************************************
//
// The following define the offsets of the comparator registers.
//
//*****************************************************************************
#define COMP_O_MIS              0x00000000  // Interrupt status register
#define COMP_O_RIS              0x00000004  // Raw interrupt status register
#define COMP_O_INTEN            0x00000008  // Interrupt enable register
#define COMP_O_REFCTL           0x00000010  // Reference voltage control reg.
#define COMP_O_ACSTAT0          0x00000020  // Comp0 status register
#define COMP_O_ACCTL0           0x00000024  // Comp0 control register
#define COMP_O_ACSTAT1          0x00000040  // Comp1 status register
#define COMP_O_ACCTL1           0x00000044  // Comp1 control register
#define COMP_O_ACSTAT2          0x00000060  // Comp2 status register
#define COMP_O_ACCTL2           0x00000064  // Comp2 control register

//*****************************************************************************
//
// The following define the bit fields in the COMP_MIS, COMP_RIS, and
// COMP_INTEN registers.
//
//*****************************************************************************
#define COMP_INT_2              0x00000004  // Comp2 interrupt
#define COMP_INT_1              0x00000002  // Comp1 interrupt
#define COMP_INT_0              0x00000001  // Comp0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the COMP_REFCTL register.
//
//*****************************************************************************
#define COMP_REFCTL_EN          0x00000200  // Reference voltage enable
#define COMP_REFCTL_RNG         0x00000100  // Reference voltage range
#define COMP_REFCTL_VREF_MASK   0x0000000F  // Reference voltage select mask
#define COMP_REFCTL_VREF_SHIFT  0

//*****************************************************************************
//
// The following define the bit fields in the COMP_ACSTAT0, COMP_ACSTAT1, and
// COMP_ACSTAT2 registers.
//
//*****************************************************************************
#define COMP_ACSTAT_OVAL        0x00000002  // Comparator output value

//*****************************************************************************
//
// The following define the bit fields in the COMP_ACCTL0, COMP_ACCTL1, and
// COMP_ACCTL2 registers.
//
//*****************************************************************************
#define COMP_ACCTL_TMASK        0x00000800  // Trigger enable
#define COMP_ACCTL_ASRCP_MASK   0x00000600  // Vin+ source select mask
#define COMP_ACCTL_ASRCP_PIN    0x00000000  // Dedicated Comp+ pin
#define COMP_ACCTL_ASRCP_PIN0   0x00000200  // Comp0+ pin
#define COMP_ACCTL_ASRCP_REF    0x00000400  // Internal voltage reference
#define COMP_ACCTL_ASRCP_RES    0x00000600  // Reserved
#define COMP_ACCTL_OEN          0x00000100  // Comparator output enable
#define COMP_ACCTL_TSVAL        0x00000080  // Trigger polarity select
#define COMP_ACCTL_TSEN_MASK    0x00000060  // Trigger sense mask
#define COMP_ACCTL_TSEN_LEVEL   0x00000000  // Trigger is level sense
#define COMP_ACCTL_TSEN_FALL    0x00000020  // Trigger is falling edge
#define COMP_ACCTL_TSEN_RISE    0x00000040  // Trigger is rising edge
#define COMP_ACCTL_TSEN_BOTH    0x00000060  // Trigger is both edges
#define COMP_ACCTL_ISLVAL       0x00000010  // Interrupt polarity select
#define COMP_ACCTL_ISEN_MASK    0x0000000C  // Interrupt sense mask
#define COMP_ACCTL_ISEN_LEVEL   0x00000000  // Interrupt is level sense
#define COMP_ACCTL_ISEN_FALL    0x00000004  // Interrupt is falling edge
#define COMP_ACCTL_ISEN_RISE    0x00000008  // Interrupt is rising edge
#define COMP_ACCTL_ISEN_BOTH    0x0000000C  // Interrupt is both edges
#define COMP_ACCTL_CINV         0x00000002  // Comparator output invert

//*****************************************************************************
//
// The following define the reset values for the comparator registers.
//
//*****************************************************************************
#define COMP_RV_MIS             0x00000000  // Interrupt status register
#define COMP_RV_RIS             0x00000000  // Raw interrupt status register
#define COMP_RV_INTEN           0x00000000  // Interrupt enable register
#define COMP_RV_REFCTL          0x00000000  // Reference voltage control reg.
#define COMP_RV_ACSTAT0         0x00000000  // Comp0 status register
#define COMP_RV_ACCTL0          0x00000000  // Comp0 control register
#define COMP_RV_ACSTAT1         0x00000000  // Comp1 status register
#define COMP_RV_ACCTL1          0x00000000  // Comp1 control register
#define COMP_RV_ACSTAT2         0x00000000  // Comp2 status register
#define COMP_RV_ACCTL2          0x00000000  // Comp2 control register

#endif // __HW_COMP_H__
