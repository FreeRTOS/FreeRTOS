//*****************************************************************************
//
// hw_hibernate.h - Defines and Macros for the Hibernation module.
//
// Copyright (c) 2007 Luminary Micro, Inc.  All rights reserved.
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

#ifndef __HW_HIBERNATE_H__
#define __HW_HIBERNATE_H__

//*****************************************************************************
//
// The following define the addresses of the hibernation module registers.
//
//*****************************************************************************
#define HIB_RTCC                0x400fc000  // Hibernate RTC counter
#define HIB_RTCM0               0x400fc004  // Hibernate RTC match 0
#define HIB_RTCM1               0x400fc008  // Hibernate RTC match 1
#define HIB_RTCLD               0x400fc00C  // Hibernate RTC load
#define HIB_CTL                 0x400fc010  // Hibernate RTC control
#define HIB_IM                  0x400fc014  // Hibernate interrupt mask
#define HIB_RIS                 0x400fc018  // Hibernate raw interrupt status
#define HIB_MIS                 0x400fc01C  // Hibernate masked interrupt stat
#define HIB_IC                  0x400fc020  // Hibernate interrupt clear
#define HIB_RTCT                0x400fc024  // Hibernate RTC trim
#define HIB_DATA                0x400fc030  // Hibernate data area
#define HIB_DATA_END            0x400fc130  // end of data area, exclusive

//*****************************************************************************
//
// The following define the bit fields in the Hibernate RTC counter register.
//
//*****************************************************************************
#define HIB_RTCC_MASK           0xffffffff  // RTC counter mask

//*****************************************************************************
//
// The following define the bit fields in the Hibernate RTC match 0 register.
//
//*****************************************************************************
#define HIB_RTCM0_MASK          0xffffffff  // RTC match 0 mask

//*****************************************************************************
//
// The following define the bit fields in the Hibernate RTC match 1 register.
//
//*****************************************************************************
#define HIB_RTCM1_MASK          0xffffffff  // RTC match 1 mask

//*****************************************************************************
//
// The following define the bit fields in the Hibernate RTC load register.
//
//*****************************************************************************
#define HIB_RTCLD_MASK          0xffffffff  // RTC load mask

//*****************************************************************************
//
// The following define the bit fields in the Hibernate control register
//
//*****************************************************************************
#define HIB_CTL_VABORT          0x00000080  // low bat abort
#define HIB_CTL_CLK32EN         0x00000040  // enable clock/oscillator
#define HIB_CTL_LOWBATEN        0x00000020  // enable low battery detect
#define HIB_CTL_PINWEN          0x00000010  // enable wake on WAKE pin
#define HIB_CTL_RTCWEN          0x00000008  // enable wake on RTC match
#define HIB_CTL_CLKSEL          0x00000004  // clock input selection
#define HIB_CTL_HIBREQ          0x00000002  // request hibernation
#define HIB_CTL_RTCEN           0x00000001  // RTC enable

//*****************************************************************************
//
// The following define the bit fields in the Hibernate interrupt mask reg.
//
//*****************************************************************************
#define HIB_IM_EXTW             0x00000008  // wake from external pin interrupt
#define HIB_IM_LOWBAT           0x00000004  // low battery interrupt
#define HIB_IM_RTCALT1          0x00000002  // RTC match 1 interrupt
#define HIB_IM_RTCALT0          0x00000001  // RTC match 0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the Hibernate raw interrupt status.
//
//*****************************************************************************
#define HIB_RIS_EXTW            0x00000008  // wake from external pin interrupt
#define HIB_RIS_LOWBAT          0x00000004  // low battery interrupt
#define HIB_RIS_RTCALT1         0x00000002  // RTC match 1 interrupt
#define HIB_RID_RTCALT0         0x00000001  // RTC match 0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the Hibernate masked int status.
//
//*****************************************************************************
#define HIB_MIS_EXTW            0x00000008  // wake from external pin interrupt
#define HIB_MIS_LOWBAT          0x00000004  // low battery interrupt
#define HIB_MIS_RTCALT1         0x00000002  // RTC match 1 interrupt
#define HIB_MID_RTCALT0         0x00000001  // RTC match 0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the Hibernate interrupt clear reg.
//
//*****************************************************************************
#define HIB_IC_EXTW             0x00000008  // wake from external pin interrupt
#define HIB_IC_LOWBAT           0x00000004  // low battery interrupt
#define HIB_IC_RTCALT1          0x00000002  // RTC match 1 interrupt
#define HIB_IC_RTCALT0          0x00000001  // RTC match 0 interrupt

//*****************************************************************************
//
// The following define the bit fields in the Hibernate RTC trim register.
//
//*****************************************************************************
#define HIB_RTCT_MASK           0x0000ffff  // RTC trim mask

//*****************************************************************************
//
// The following define the bit fields in the Hibernate data register.
//
//*****************************************************************************
#define HIB_DATA_MASK           0xffffffff  // NV memory data mask

#endif // __HW_HIBERNATE_H__
