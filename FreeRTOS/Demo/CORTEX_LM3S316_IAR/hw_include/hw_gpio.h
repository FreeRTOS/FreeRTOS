//*****************************************************************************
//
// hw_gpio.h - Defines and Macros for GPIO hardware.
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

#ifndef __HW_GPIO_H__
#define __HW_GPIO_H__

//*****************************************************************************
//
// GPIO Register Offsets.
//
//*****************************************************************************
#define GPIO_O_DATA             0x00000000  // Data register.
#define GPIO_O_DIR              0x00000400  // Data direction register.
#define GPIO_O_IS               0x00000404  // Interrupt sense register.
#define GPIO_O_IBE              0x00000408  // Interrupt both edges register.
#define GPIO_O_IEV              0x0000040C  // Intterupt event register.
#define GPIO_O_IM               0x00000410  // Interrupt mask register.
#define GPIO_O_RIS              0x00000414  // Raw interrupt status register.
#define GPIO_O_MIS              0x00000418  // Masked interrupt status reg.
#define GPIO_O_ICR              0x0000041C  // Interrupt clear register.
#define GPIO_O_AFSEL            0x00000420  // Mode control select register.
#define GPIO_O_DR2R             0x00000500  // 2ma drive select register.
#define GPIO_O_DR4R             0x00000504  // 4ma drive select register.
#define GPIO_O_DR8R             0x00000508  // 8ma drive select register.
#define GPIO_O_ODR              0x0000050C  // Open drain select register.
#define GPIO_O_PUR              0x00000510  // Pull up select register.
#define GPIO_O_PDR              0x00000514  // Pull down select register.
#define GPIO_O_SLR              0x00000518  // Slew rate control enable reg.
#define GPIO_O_DEN              0x0000051C  // Digital input enable register.
#define GPIO_O_PeriphID4        0x00000FD0  //
#define GPIO_O_PeriphID5        0x00000FD4  //
#define GPIO_O_PeriphID6        0x00000FD8  //
#define GPIO_O_PeriphID7        0x00000FDC  //
#define GPIO_O_PeriphID0        0x00000FE0  //
#define GPIO_O_PeriphID1        0x00000FE4  //
#define GPIO_O_PeriphID2        0x00000FE8  //
#define GPIO_O_PeriphID3        0x00000FEC  //
#define GPIO_O_PCellID0         0x00000FF0  //
#define GPIO_O_PCellID1         0x00000FF4  //
#define GPIO_O_PCellID2         0x00000FF8  //
#define GPIO_O_PCellID3         0x00000FFC  //

//*****************************************************************************
//
// GPIO Register reset values.
//
//*****************************************************************************
#define GPIO_RV_DATA            0x00000000  // Data register reset value.
#define GPIO_RV_DIR             0x00000000  // Data direction reg RV.
#define GPIO_RV_IS              0x00000000  // Interrupt sense reg RV.
#define GPIO_RV_IBE             0x00000000  // Interrupt both edges reg RV.
#define GPIO_RV_IEV             0x00000000  // Intterupt event reg RV.
#define GPIO_RV_IM              0x00000000  // Interrupt mask reg RV.
#define GPIO_RV_RIS             0x00000000  // Raw interrupt status reg RV.
#define GPIO_RV_MIS             0x00000000  // Masked interrupt status reg RV.
#define GPIO_RV_IC              0x00000000  // Interrupt clear reg RV.
#define GPIO_RV_AFSEL           0x00000000  // Mode control select reg RV.
#define GPIO_RV_DR2R            0x000000FF  // 2ma drive select reg RV.
#define GPIO_RV_DR4R            0x00000000  // 4ma drive select reg RV.
#define GPIO_RV_DR8R            0x00000000  // 8ma drive select reg RV.
#define GPIO_RV_ODR             0x00000000  // Open drain select reg RV.
#define GPIO_RV_PUR             0x000000FF  // Pull up select reg RV.
#define GPIO_RV_PDR             0x00000000  // Pull down select reg RV.
#define GPIO_RV_SLR             0x00000000  // Slew rate control enable reg RV.
#define GPIO_RV_DEN             0x000000FF  // Digital input enable reg RV.
#define GPIO_RV_PeriphID4       0x00000000  //
#define GPIO_RV_PeriphID5       0x00000000  //
#define GPIO_RV_PeriphID6       0x00000000  //
#define GPIO_RV_PeriphID7       0x00000000  //
#define GPIO_RV_PeriphID0       0x00000061  //
#define GPIO_RV_PeriphID1       0x00000010  //
#define GPIO_RV_PeriphID2       0x00000004  //
#define GPIO_RV_PeriphID3       0x00000000  //
#define GPIO_RV_PCellID0        0x0000000D  //
#define GPIO_RV_PCellID1        0x000000F0  //
#define GPIO_RV_PCellID2        0x00000005  //
#define GPIO_RV_PCellID3        0x000000B1  //

#endif //  __HW_GPIO_H__
