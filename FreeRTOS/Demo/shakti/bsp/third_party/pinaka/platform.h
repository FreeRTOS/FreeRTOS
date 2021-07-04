/*
platform.h - header file for pinaka E class SoC on artix7_35t

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
/******	e-rv32imac-35t ********
 SPI   * 2
 GPIO  * 32
 UART  * 2
 I2C   * 2
 PLIC  * 1
 CLINT * 1
 XADC  * 1
 BRAM  : 128kiB
 Boot
 PWM   * 6
 pinmux
********************************/
   

#ifndef PLATFORM_H
#define PLATFORM_H

/*
 *@brief RISCV - E CLASS SOC Memory mapping
 */

/*! Core Local Interruptor CLINT */
#define CLINT_BASE 0x020000000
#define MTIME      CLINT_BASE + 0xBFF8
#define MTIMECMP   CLINT_BASE + 0x4000

#define CLOCK_FREQUENCY 50000000

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
#define PWM_OFFSET 0x00000100 /*Offset value to be incremented for each interface*/

/*!Serial Peripheral Interface Offsets */
#define SPI0_START 0x00020000 /* Serial Peripheral Interface 0 */
#define SPI1_START 0x00020100 /* Serial Peripheral Interface 1 */

/*!Universal Synchronous Receiver Transmitter Interface Offsets */
#define UART0_START 0x00011300 /*! UART 0 */
#define UART_OFFSET 0x100
#define MAX_UART_COUNT 3

/*! Inter Integrated Circuit (I2C) Interface */
#define I2C0_BASE 0x00040000 /*! I2C Start Address */
#define I2C_OFFSET 0x1400
#define MAX_I2C_COUNT 2

/*! Xilinx Analog to Digital converter */
#define XADC_BASE_ADDRESS 0x00041000

/*! pinmux*/
#define PINMUX_START 0x41500 
#define PINMUX_CONFIGURE_REG 0x41510

/*! Programmable Logic Interrupt Interface */
#define PLIC_BASE_ADDRESS 0x0C000000 /*! PLIC Interface Start */
#define PLIC_INTERRUPT_1   1	/* PWM 0   */
#define PLIC_INTERRUPT_2   2	/* PWM 1   */
#define PLIC_INTERRUPT_3   3	/* PWM 2   */
#define PLIC_INTERRUPT_4   4	/* PWM 3   */
#define PLIC_INTERRUPT_5   5	/* PWM 4   */
#define PLIC_INTERRUPT_6   6	/* PWM 5   */
#define PLIC_INTERRUPT_7   7	/* GPIO 0  */
#define PLIC_INTERRUPT_8   8	/* GPIO 1  */
#define PLIC_INTERRUPT_9   9	/* GPIO 2  */
#define PLIC_INTERRUPT_10  10	/* GPIO 3  */
#define PLIC_INTERRUPT_11  11	/* GPIO 4  */
#define PLIC_INTERRUPT_12  12	/* GPIO 5  */
#define PLIC_INTERRUPT_13  13	/* GPIO 6  */
#define PLIC_INTERRUPT_14  14	/* GPIO 7  */
#define PLIC_INTERRUPT_15  15	/* GPIO 8  */
#define PLIC_INTERRUPT_16  16	/* GPIO 9  */
#define PLIC_INTERRUPT_17  17	/* GPIO 10 */
#define PLIC_INTERRUPT_18  18	/* GPIO 11 */
#define PLIC_INTERRUPT_19  19	/* GPIO 12 */
#define PLIC_INTERRUPT_20  20	/* GPIO 13 */
#define PLIC_INTERRUPT_21  21	/* GPIO 14 */
#define PLIC_INTERRUPT_22  22	/* GPIO 15 */
#define PLIC_INTERRUPT_23  23	/* I2C 0   */
#define PLIC_INTERRUPT_24  24	/* I2C 1   */
#define PLIC_INTERRUPT_25  25 	/* uart 0  */
#define PLIC_INTERRUPT_26  26 	/* uart 1  */
#define PLIC_INTERRUPT_27  27 	/* uart 2  */
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
#define GPIO16 (1 << 16)
#define GPIO17 (1 << 17)
#define GPIO18 (1 << 18)
#define GPIO19 (1 << 19)
#define GPIO20 (1 << 20)
#define GPIO21 (1 << 21)
#define GPIO22 (1 << 22)
#define GPIO23 (1 << 23)
#define GPIO24 (1 << 24)
#define GPIO25 (1 << 25)
#define GPIO26 (1 << 26)
#define GPIO27 (1 << 27)
#define GPIO28 (1 << 28)
#define GPIO29 (1 << 29)
#define GPIO30 (1 << 30)
#define GPIO31 (1 << 31)
#define GPIO_COUNT  0x20

#endif
