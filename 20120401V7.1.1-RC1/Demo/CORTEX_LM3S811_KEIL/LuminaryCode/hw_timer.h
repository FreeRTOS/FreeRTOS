//*****************************************************************************
//
// hw_timer.h - Defines and macros used when accessing the timer.
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
// This is part of revision 816 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __HW_TIMER_H__
#define __HW_TIMER_H__

//*****************************************************************************
//
// The following define the offsets of the timer registers.
//
//*****************************************************************************
#define TIMER_O_CFG             0x00000000  // Configuration register
#define TIMER_O_TAMR            0x00000004  // TimerA mode register
#define TIMER_O_TBMR            0x00000008  // TimerB mode register
#define TIMER_O_CTL             0x0000000C  // Control register
#define TIMER_O_IMR             0x00000018  // Interrupt mask register
#define TIMER_O_RIS             0x0000001C  // Interrupt status register
#define TIMER_O_MIS             0x00000020  // Masked interrupt status reg.
#define TIMER_O_ICR             0x00000024  // Interrupt clear register
#define TIMER_O_TAILR           0x00000028  // TimerA interval load register
#define TIMER_O_TBILR           0x0000002C  // TimerB interval load register
#define TIMER_O_TAMATCHR        0x00000030  // TimerA match register
#define TIMER_O_TBMATCHR        0x00000034  // TimerB match register
#define TIMER_O_TAPR            0x00000038  // TimerA prescale register
#define TIMER_O_TBPR            0x0000003C  // TimerB prescale register
#define TIMER_O_TAPMR           0x00000040  // TimerA prescale match register
#define TIMER_O_TBPMR           0x00000044  // TimerB prescale match register
#define TIMER_O_TAR             0x00000048  // TimerA register
#define TIMER_O_TBR             0x0000004C  // TimerB register

//*****************************************************************************
//
// The following define the reset values of the timer registers.
//
//*****************************************************************************
#define TIMER_RV_CFG            0x00000000  // Configuration register RV
#define TIMER_RV_TAMR           0x00000000  // TimerA mode register RV
#define TIMER_RV_TBMR           0x00000000  // TimerB mode register RV
#define TIMER_RV_CTL            0x00000000  // Control register RV
#define TIMER_RV_IMR            0x00000000  // Interrupt mask register RV
#define TIMER_RV_RIS            0x00000000  // Interrupt status register RV
#define TIMER_RV_MIS            0x00000000  // Masked interrupt status reg RV
#define TIMER_RV_ICR            0x00000000  // Interrupt clear register RV
#define TIMER_RV_TAILR          0xFFFFFFFF  // TimerA interval load reg RV
#define TIMER_RV_TBILR          0x0000FFFF  // TimerB interval load reg RV
#define TIMER_RV_TAMATCHR       0xFFFFFFFF  // TimerA match register RV
#define TIMER_RV_TBMATCHR       0x0000FFFF  // TimerB match register RV
#define TIMER_RV_TAPR           0x00000000  // TimerA prescale register RV
#define TIMER_RV_TBPR           0x00000000  // TimerB prescale register RV
#define TIMER_RV_TAPMR          0x00000000  // TimerA prescale match reg RV
#define TIMER_RV_TBPMR          0x00000000  // TimerB prescale match regi RV
#define TIMER_RV_TAR            0xFFFFFFFF  // TimerA register RV
#define TIMER_RV_TBR            0x0000FFFF  // TimerB register RV

//*****************************************************************************
//
// The following define the bit fields in the TIMER_CFG register.
//
//*****************************************************************************
#define TIMER_CFG_CFG_MSK       0x00000007  // Configuration options mask
#define TIMER_CFG_16_BIT        0x00000004  // Two 16 bit timers
#define TIMER_CFG_32_BIT_RTC    0x00000001  // 32 bit RTC
#define TIMER_CFG_32_BIT_TIMER  0x00000000  // 32 bit timer

//*****************************************************************************
//
// The following define the bit fields in the TIMER_TnMR register.
//
//*****************************************************************************
#define TIMER_TNMR_TNAMS        0x00000008  // Alternate mode select
#define TIMER_TNMR_TNCMR        0x00000004  // Capture mode - count or time
#define TIMER_TNMR_TNTMR_MSK    0x00000003  // Timer mode mask
#define TIMER_TNMR_TNTMR_CAP    0x00000003  // Mode - capture
#define TIMER_TNMR_TNTMR_PERIOD 0x00000002  // Mode - periodic
#define TIMER_TNMR_TNTMR_1_SHOT 0x00000001  // Mode - one shot

//*****************************************************************************
//
// The following define the bit fields in the TIMER_CTL register.
//
//*****************************************************************************
#define TIMER_CTL_TBPWML        0x00004000  // TimerB PWM output level invert
#define TIMER_CTL_TBOTE         0x00002000  // TimerB output trigger enable
#define TIMER_CTL_TBEVENT_MSK   0x00000C00  // TimerB event mode mask
#define TIMER_CTL_TBEVENT_BOTH  0x00000C00  // TimerB event mode - both edges
#define TIMER_CTL_TBEVENT_NEG   0x00000400  // TimerB event mode - neg edge
#define TIMER_CTL_TBEVENT_POS   0x00000000  // TimerB event mode - pos edge
#define TIMER_CTL_TBSTALL       0x00000200  // TimerB stall enable
#define TIMER_CTL_TBEN          0x00000100  // TimerB enable
#define TIMER_CTL_TAPWML        0x00000040  // TimerA PWM output level invert
#define TIMER_CTL_TAOTE         0x00000020  // TimerA output trigger enable
#define TIMER_CTL_RTCEN         0x00000010  // RTC counter enable
#define TIMER_CTL_TAEVENT_MSK   0x0000000C  // TimerA event mode mask
#define TIMER_CTL_TAEVENT_BOTH  0x0000000C  // TimerA event mode - both edges
#define TIMER_CTL_TAEVENT_NEG   0x00000004  // TimerA event mode - neg edge
#define TIMER_CTL_TAEVENT_POS   0x00000000  // TimerA event mode - pos edge
#define TIMER_CTL_TASTALL       0x00000002  // TimerA stall enable
#define TIMER_CTL_TAEN          0x00000001  // TimerA enable

//*****************************************************************************
//
// The following define the bit fields in the TIMER_IMR register.
//
//*****************************************************************************
#define TIMER_IMR_CBEIM         0x00000400  // CaptureB event interrupt mask
#define TIMER_IMR_CBMIM         0x00000200  // CaptureB match interrupt mask
#define TIMER_IMR_TBTOIM        0x00000100  // TimerB time out interrupt mask
#define TIMER_IMR_RTCIM         0x00000008  // RTC interrupt mask
#define TIMER_IMR_CAEIM         0x00000004  // CaptureA event interrupt mask
#define TIMER_IMR_CAMIM         0x00000002  // CaptureA match interrupt mask
#define TIMER_IMR_TATOIM        0x00000001  // TimerA time out interrupt mask

//*****************************************************************************
//
// The following define the bit fields in the TIMER_RIS register.
//
//*****************************************************************************
#define TIMER_RIS_CBERIS        0x00000400  // CaptureB event raw int status
#define TIMER_RIS_CBMRIS        0x00000200  // CaptureB match raw int status
#define TIMER_RIS_TBTORIS       0x00000100  // TimerB time out raw int status
#define TIMER_RIS_RTCRIS        0x00000008  // RTC raw int status
#define TIMER_RIS_CAERIS        0x00000004  // CaptureA event raw int status
#define TIMER_RIS_CAMRIS        0x00000002  // CaptureA match raw int status
#define TIMER_RIS_TATORIS       0x00000001  // TimerA time out raw int status

//*****************************************************************************
//
// The following define the bit fields in the TIMER_MIS register.
//
//*****************************************************************************
#define TIMER_RIS_CBEMIS        0x00000400  // CaptureB event masked int status
#define TIMER_RIS_CBMMIS        0x00000200  // CaptureB match masked int status
#define TIMER_RIS_TBTOMIS       0x00000100  // TimerB time out masked int stat
#define TIMER_RIS_RTCMIS        0x00000008  // RTC masked int status
#define TIMER_RIS_CAEMIS        0x00000004  // CaptureA event masked int status
#define TIMER_RIS_CAMMIS        0x00000002  // CaptureA match masked int status
#define TIMER_RIS_TATOMIS       0x00000001  // TimerA time out masked int stat

//*****************************************************************************
//
// The following define the bit fields in the TIMER_ICR register.
//
//*****************************************************************************
#define TIMER_ICR_CBECINT       0x00000400  // CaptureB event interrupt clear
#define TIMER_ICR_CBMCINT       0x00000200  // CaptureB match interrupt clear
#define TIMER_ICR_TBTOCINT      0x00000100  // TimerB time out interrupt clear
#define TIMER_ICR_RTCCINT       0x00000008  // RTC interrupt clear
#define TIMER_ICR_CAECINT       0x00000004  // CaptureA event interrupt clear
#define TIMER_ICR_CAMCINT       0x00000002  // CaptureA match interrupt clear
#define TIMER_ICR_TATOCINT      0x00000001  // TimerA time out interrupt clear

//*****************************************************************************
//
// The following define the bit fields in the TIMER_TAILR register.
//
//*****************************************************************************
#define TIMER_TAILR_TAILRH      0xFFFF0000  // TimerB load val in 32 bit mode
#define TIMER_TAILR_TAILRL      0x0000FFFF  // TimerA interval load value

//*****************************************************************************
//
// The following defines the bit fields in the TIMER_TBILR register.
//
//*****************************************************************************
#define TIMER_TBILR_TBILRL      0x0000FFFF  // TimerB interval load value

//*****************************************************************************
//
// The following define the bit fields in the TIMER_TAMATCHR register.
//
//*****************************************************************************
#define TIMER_TAMATCHR_TAMRH    0xFFFF0000  // TimerB match val in 32 bit mode
#define TIMER_TAMATCHR_TAMRL    0x0000FFFF  // TimerA match value

//*****************************************************************************
//
// The following defines the bit fields in the TIMER_TBMATCHR register.
//
//*****************************************************************************
#define TIMER_TBMATCHR_TBMRL    0x0000FFFF  // TimerB match load value

//*****************************************************************************
//
// The following defines the bit fields in the TIMER_TnPR register.
//
//*****************************************************************************
#define TIMER_TNPR_TNPSR        0x000000FF  // TimerN prescale value

//*****************************************************************************
//
// The following defines the bit fields in the TIMER_TnPMR register.
//
//*****************************************************************************
#define TIMER_TNPMR_TNPSMR      0x000000FF  // TimerN prescale match value

//*****************************************************************************
//
// The following define the bit fields in the TIMER_TAR register.
//
//*****************************************************************************
#define TIMER_TAR_TARH          0xFFFF0000  // TimerB val in 32 bit mode
#define TIMER_TAR_TARL          0x0000FFFF  // TimerA value

//*****************************************************************************
//
// The following defines the bit fields in the TIMER_TBR register.
//
//*****************************************************************************
#define TIMER_TBR_TBRL          0x0000FFFF  // TimerB value

#endif // __HW_TIMER_H__
