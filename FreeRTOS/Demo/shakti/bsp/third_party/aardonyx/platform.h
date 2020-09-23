/*
platform.h - header file for Aardonyx E class SoC

Created by Sathya Narayanan N
Email id: sathya281@gmail.com

    Copyright (C) 2019  IIT Madras. All rights reserved.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

*/

#ifndef PLATFORM_H
#define PLATFORM_H

/*
 *@brief RISCV - E CLASS SOC Memory mapping
 */

#define CLOCK_FREQUENCY 40000000

/*! Core Local Interruptor CLINT */

#define CLINT_BASE 0x020000000
#define MTIME      CLINT_BASE + 0xBFF8
#define MTIMECMP   CLINT_BASE + 0x4000

#define MCAUSE_INT         0x80000000
#define MCAUSE_CAUSE       0x7FFFFFFF

#define PINMUX_CONFIGURE_REG 0x40310

/*!Debugger Offset */
#define DBG_MEM_START 0x00000010

/*!Tightly Coupled Memory(TCM) Offset. Size 128kB */
#define TCM_MEM_START 0x80000000 /*! DDR3 Memory Start address */

/*!Tightly Coupled Memory(TCM) Size. Size 128kB */
#define TCM_MEM_SIZE 0x20000 /*! DDR3 Memory Size */

/*!Percentage of Free Memory to be used as stack (0-100). The remaining space will be used by heap */
#define STACK_PERCENTAGE 50 /*! DDR3 Memory Size */

/*!Percentage of Free Memory to be used as stack (0-100). The remaining space will be used by heap */
#define HEAP_PERCENTAGE 50 /*! DDR3 Memory Size */

/*!Pulse Width Modulation Start Offsets */
#define PWM_BASE_ADDRESS 0x00030000 /*PWM Base address*/
#define PWM_MODULE_OFFSET 0x00000100 /*Offset value to be incremented for each interface*/

/*!Serial Peripheral Interface Offsets */
#define SPI0_START 0x00020000 /* Serial Peripheral Interface 0 */
#define SPI1_START 0x00020100 /* Serial Peripheral Interface 1 */
#define SPI2_START 0x00020200 /* Serial Peripheral Interface 2 */

/*!Universal Synchronous Receiver Transmitter Interface Offsets */
#define UART0_START 0x00011300 /*! UART 0 */
#define UART1_START 0x00011400 /*! UART 1 */
#define UART2_START 0x00011500 /*! UART 2 */
#define UART_OFFSET 0x100
#define UART_BASE 0x11300
#define MAX_UART_COUNT 3

#define PINMUX_CONFIGURE_REG 0x40310


/*! Inter Integrated Circuit (I2C) Interface */
#define I2C0_BASE 0x00040000
#define I2C_OFFSET 0x400
#define MAX_I2C_COUNT 2

/*! Programmable Logic Interrupt Interface */
#define PLIC_BASE_ADDRESS 0x0C000000 /*! PLIC Interface Start */
#define PLIC_INTERRUPT_1   1
#define PLIC_INTERRUPT_2   2
#define PLIC_INTERRUPT_3   3
#define PLIC_INTERRUPT_4   4
#define PLIC_INTERRUPT_5   5
#define PLIC_INTERRUPT_6   6
#define PLIC_INTERRUPT_7   7
#define PLIC_INTERRUPT_8   8
#define PLIC_INTERRUPT_9   9
#define PLIC_INTERRUPT_10  10
#define PLIC_INTERRUPT_11  11
#define PLIC_INTERRUPT_12  12
#define PLIC_INTERRUPT_13  13
#define PLIC_INTERRUPT_14  14
#define PLIC_INTERRUPT_15  15
#define PLIC_INTERRUPT_16  16
#define PLIC_INTERRUPT_17  17
#define PLIC_INTERRUPT_18  18
#define PLIC_INTERRUPT_19  19
#define PLIC_INTERRUPT_20  20
#define PLIC_INTERRUPT_21  21
#define PLIC_INTERRUPT_22  22
#define PLIC_INTERRUPT_23  23
#define PLIC_INTERRUPT_24  24
#define PLIC_INTERRUPT_25  25 //uart 0
#define PLIC_INTERRUPT_26  26 //uart 1
#define PLIC_INTERRUPT_27  27 //uart 2

#define PLIC_MAX_INTERRUPT_SRC 28

/*!General Purpose Input / Output */
#define GPIO_START 0x00040100 //GPIO Start Address */
#define GPIO_OFFSET 0x08 /*!Generic offset used to access GPIO registers*/
#define PLIC_GPIO_OFFSET 6

/*
 * General Purpose IOs supported
 */

#define GPIO0  (1 <<  0)
#define GPIO1  (1 <<  1)
#define GPIO2  (1 <<  2)
#define GPIO3  (1 <<  3)
#define GPIO4  (1 <<  4)
#define GPIO5  (1 <<  5)
#define GPIO6  (1 <<  6)
#define GPIO7  (1 <<  7)
#define GPIO8  (1 <<  8)
#define GPIO9  (1 <<  9)
#define GPIO10 (1 << 10)
#define GPIO11 (1 << 11)
#define GPIO12 (1 << 12)
#define GPIO13 (1 << 13)
#define GPIO14 (1 << 14)
#define GPIO15 (1 << 15)

#define GPIO_COUNT  0x10

#endif
