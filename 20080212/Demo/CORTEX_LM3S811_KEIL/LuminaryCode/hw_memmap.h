//*****************************************************************************
//
// hw_memmap.h - Macros defining the memory map of Stellaris.
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

#ifndef __HW_MEMMAP_H__
#define __HW_MEMMAP_H__

//*****************************************************************************
//
// The following define the base address of the memories and peripherals.
//
//*****************************************************************************
#define FLASH_BASE              0x00000000  // FLASH memory
#define SRAM_BASE               0x20000000  // SRAM memory
#define WATCHDOG_BASE           0x40000000  // Watchdog
#define GPIO_PORTA_BASE         0x40004000  // GPIO Port A
#define GPIO_PORTB_BASE         0x40005000  // GPIO Port B
#define GPIO_PORTC_BASE         0x40006000  // GPIO Port C
#define GPIO_PORTD_BASE         0x40007000  // GPIO Port D
#define SSI_BASE                0x40008000  // SSI
#define UART0_BASE              0x4000C000  // UART0
#define UART1_BASE              0x4000D000  // UART1
#define I2C_MASTER_BASE         0x40020000  // I2C Master
#define I2C_SLAVE_BASE          0x40020800  // I2C Slave
#define GPIO_PORTE_BASE         0x40024000  // GPIO Port E
#define PWM_BASE                0x40028000  // PWM
#define QEI_BASE                0x4002C000  // QEI
#define TIMER0_BASE             0x40030000  // Timer0
#define TIMER1_BASE             0x40031000  // Timer1
#define TIMER2_BASE             0x40032000  // Timer2
#define ADC_BASE                0x40038000  // ADC
#define COMP_BASE               0x4003C000  // Analog comparators
#define FLASH_CTRL_BASE         0x400FD000  // FLASH Controller
#define SYSCTL_BASE             0x400FE000  // System Control
#define ITM_BASE                0xE0000000  // Instrumentation Trace Macrocell
#define DWT_BASE                0xE0001000  // Data Watchpoint and Trace
#define FPB_BASE                0xE0002000  // FLASH Patch and Breakpoint
#define NVIC_BASE               0xE000E000  // Nested Vectored Interrupt Ctrl
#define TPIU_BASE               0xE0040000  // Trace Port Interface Unit

#endif // __HW_MEMMAP_H__
