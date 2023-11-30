/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of
* this software. By using this software, you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_bsp_config_reference.c
* Device(s)    : RX111
* Description  : The file r_bsp_config.h is used to configure your BSP. r_bsp_config.h should be included
*                somewhere in your package so that the r_bsp code has access to it. This file (r_bsp_config_reference.h)
*                is just a reference file that the user can use to make their own r_bsp_config.h file.
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*         : 07.11.2012 0.01    Beta Release
***********************************************************************************************************************/
#ifndef R_BSP_CONFIG_REF_HEADER_FILE
#define R_BSP_CONFIG_REF_HEADER_FILE

/***********************************************************************************************************************
Configuration Options
***********************************************************************************************************************/
/* Enter the product part number for your MCU. This information will be used to obtain information about your MCU such
   as package and memory size.
   To help parse this information, the part number will be defined using multiple macros.
   R 5 F 51 11 5 A D FM
   | | | |  |  | | | |  Macro Name              Description
   | | | |  |  | | | |__MCU_PART_PACKAGE      = Package type, number of pins, and pin pitch
   | | | |  |  | | |____not used              = Products with wide temperature range (D: -40 to 85C G: -40 to 105C)
   | | | |  |  | |______not used              = Blank
   | | | |  |  |________MCU_PART_MEMORY_SIZE  = ROM, RAM, and Data Flash Capacity
   | | | |  |___________MCU_PART_GROUP        = Group name
   | | | |______________MCU_PART_SERIES       = Series name
   | | |________________MCU_PART_MEMORY_TYPE  = Type of memory (Flash)
   | |__________________not used              = Renesas MCU
   |____________________not used              = Renesas semiconductor product.
   */

/* Package type. Set the macro definition based on values below:
   Character(s) = Value for macro = Package Type/Number of Pins/Pin Pitch
   FM           = 0x0             = LFQFP/64/0.50
   FK           = 0x1             = LQFP/64/0.80
   LF           = 0x2             = TFLGA/64/0.50
   FL           = 0x3             = LFQFP/48/0.50
   NE           = 0x4             = VQFN/48/0.50
   NC           = 0x5             = HWQFN/36/0.50
   LM           = 0x6             = WFLGA/36/0.50
   SB           = 0x7             = SSOP/36/0.80
*/
#define MCU_PART_PACKAGE        (0x0)

/* ROM, RAM, and Data Flash Capacity.
   Character(s) = Value for macro = ROM Size/Ram Size/Data Flash Size
   5            = 0x5             = 128KB/16KB/8KB
   4            = 0x4             = 96KB/16KB/8KB
   3            = 0x3             = 64KB/10KB/8KB
   1            = 0x1             = 32KB/10KB/8KB
   J            = 0x0             = 16KB/8KB/8KB
*/
#define MCU_PART_MEMORY_SIZE    (0x5)

/* Group name.
   Character(s) = Value for macro = Description
   10           = 0x0             = RX110 Group
   11           = 0x1             = RX111 Group
*/
#define MCU_PART_GROUP          (0x1)

/* Series name.
   Character(s) = Value for macro = Description
   51           = 0x0             = RX100 Series
*/
#define MCU_PART_SERIES         (0x0)

/* Memory type.
   Character(s) = Value for macro = Description
   F            = 0x0             = Flash memory version
*/
#define MCU_PART_MEMORY_TYPE    (0x0)

/* The 'BSP_DECLARE_STACK' macro is checked so that the stack is only declared in one place (resetprg.c). Every time a
   '#pragma stacksize' is encountered, the stack size is increased. This prevents multiplication of stack size. */
#if defined(BSP_DECLARE_STACK)
/* User Stack size in bytes. The Renesas RX toolchain sets the stack size using the #pragma stacksize directive. */
#pragma stacksize su=0x400
/* Interrupt Stack size in bytes. The Renesas RX toolchain sets the stack size using the #pragma stacksize directive. */
#pragma stacksize si=0x100
#endif

/* Heap size in bytes. */
#define HEAP_BYTES              (0x001)

/* After reset MCU will operate in Supervisor mode. To switch to User mode, set this macro to '1'. For more information
   on the differences between these 2 modes see the CPU >> Processor Mode section of your MCU's hardware manual.
   0 = Stay in Supervisor mode.
   1 = Switch to User mode.
*/
#define RUN_IN_USER_MODE        (0)


/* This macro lets other modules no if a RTOS is being used.
   0 = RTOS is not used.
   1 = RTOS is used.
*/
#define RTOS_USED               (0)

/* Clock source select (CKSEL).
   0 = Low Speed On-Chip Oscillator  (LOCO)
   1 = High Speed On-Chip Oscillator (HOCO)
   2 = Main Clock Oscillator
   3 = Sub-Clock Oscillator
   4 = PLL Circuit
*/
#define CLOCK_SOURCE            (4)	// GI org 4

/* Clock configuration options.
   The input clock frequency is specified and then the system clocks are set by specifying the multipliers used. The
   multiplier settings are used to set the clock registers in resetprg.c. If a 16MHz clock is used and the
   ICLK is 24MHz, PCLKB is 24MHz, FCLK is 24MHz, PCLKD is 24MHz, and CKO is 1MHz then the
   settings would be:

   XTAL_HZ = 16000000
   PLL_DIV = 2
   PLL_MUL = 6 (16MHz x 3 = 48MHz)
   ICK_DIV =  2      : System Clock (ICLK)        = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / ICK_DIV)  = 24MHz
   PCKB_DIV = 2      : Peripheral Clock B (PCLKB) = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / PCKB_DIV) = 24MHz
   PCKD_DIV = 2      : Peripheral Clock D (PCLKD) = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / PCKD_DIV) = 24MHz
   FCK_DIV =  2      : Flash IF Clock (FCLK)      = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / FCK_DIV)  = 24MHz
*/
/* XTAL - Input clock frequency in Hz */
#define XTAL_HZ                 (16000000)
/* PLL Input Frequency Divider Select (PLIDIV).
   Available divisors = /1 (no division), /2, /4
*/
#define PLL_DIV                 (2)		// GI org 2
/* PLL Frequency Multiplication Factor Select (STC).
   Available multipliers = x6, x8
*/
#define PLL_MUL                 (6)		// GI org 6
/* System Clock Divider (ICK).
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define ICK_DIV                 (2)		// NOTE: ICLK CANNOT BE SLOWER THAN PCLK!
/* Peripheral Module Clock B Divider (PCKB).
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define PCKB_DIV                (2)		// GI org 2
/* Peripheral Module Clock D Divider (PCKD).
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define PCKD_DIV                (2)
/* Flash IF Clock Divider (FCK).
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define FCK_DIV                 (2)

/* Below are callback functions that can be used for detecting MCU exceptions, undefined interrupt sources, and
   bus errors. If the user wishes to be alerted of these events then they will need to define the macro as a
   function to be called when the event occurs. For example, if the user wanted the function
   excep_undefined_instr_isr() to be called when an undefined interrupt source ISR is triggered then they would
   do the following:
   #define UNDEFINED_INT_ISR_CALLBACK   undefined_interrupt_cb
   If the user does not wish to be alerted of these events then they should comment out the macros.

   NOTE: When a callback function is called it will be called from within a ISR. This means that the function
         will essentially be an interrupt and will hold off other interrupts that occur in the system while it
         is executing. For this reason, it is recommended to keep these callback functions short as to not
         decrease the real-time response of your system.
*/
/* Callback for Supervisor Instruction Violation Exception. */
//#define EXCEP_SUPERVISOR_ISR_CALLBACK           supervisor_instr_cb

/* Callback for Undefined Instruction Exception. */
//#define EXCEP_UNDEFINED_INSTR_ISR_CALLBACK      undefined_instr_cb

/* Callback for Non-maskable Interrupt. */
//#define NMI_ISR_CALLBACK                        nmi_cb

/* Callback for all undefined interrupt vectors. User can set a breakpoint in this function to determine which source
   is creating unwanted interrupts. */
//#define UNDEFINED_INT_ISR_CALLBACK              undefined_interrupt_cb

/* Callback for Bus Error Interrupt. */
//#define BUS_ERROR_ISR_CALLBACK                  bus_error_cb

/* The user has the option of separately choosing little or big endian for the User Application Area */

/* Endian mode for User Application.
   0    = Big Endian
   Else = Little Endian (Default)
*/
#define USER_APP_ENDIAN     (1)


/* Configure WDT and IWDT settings.
   OFS0 - Option Function Select Register 0
       OFS0 - Option Function Select Register 0
       b31:b15 Reserved (set to 1)
       b14     IWDTSLCSTP - IWDT Sleep Mode Count Stop Control - (0=can't stop count, 1=stop w/some low power modes)
       b13     Reserved (set to 1)
       b12     IWDTRSTIRQS - IWDT Reset Interrupt Request - What to do on underflow (0=take interrupt, 1=reset MCU)
       b11:b10 IWDTRPSS - IWDT Window Start Position Select - (0=25%, 1=50%, 2=75%, 3=100%,don't use)
       b9:b8   IWDTRPES - IWDT Window End Position Select - (0=75%, 1=50%, 2=25%, 3=0%,don't use)
       b7:b4   IWDTCKS - IWDT Clock Frequency Division Ratio - (0=none, 2=/16, 3 = /32, 4=/64, 0xF=/128, 5=/256)
       b3:b2   IWDTTOPS - IWDT Timeout Period Select - (0=128 cycles, 1=512, 2=1024, 3=2048)
       b1      IWDTSTRT - IWDT Start Mode Select - (0=auto-start after reset, 1=halt after reset)
       b0      Reserved (set to 1) */
#define OFS0_REG_VALUE  (0xFFFFFFFF) //Disable by default

/* Configure whether voltage detection 1 circuit and HOCO are enabled after reset.
       OFS1 - Option Function Select Register 1
       b31:b9 Reserved (set to 1)
       b8     HOCOEN - Enable/disable HOCO oscillation after a reset (0=enable, 1=disable)
       b7:b4  STUPLVD1LVL - Startup Voltage Monitoring 1 Reset Detection Level Select
                0 1 0 0: 3.10 V
				0 1 0 1: 3.00 V
				0 1 1 0: 2.90 V
				0 1 1 1: 2.79 V
				1 0 0 0: 2.68 V
				1 0 0 1: 2.58 V
				1 0 1 0: 2.48 V
				1 0 1 1: 2.06 V
				1 1 0 0: 1.96 V
				1 1 0 1: 1.86 V
       b3:b2  Reserved (set to 1)
       b2     STUPLVD1REN - Startup Voltage Monitoring 1 Reset Enable (1=monitoring disabled)
       b0     FASTSTUP - Power-On Fast Startup Time (1=normal; read only) */
#define OFS1_REG_VALUE  (0xFFFFFFFF) //Disable by default

/* Initializes C input & output library functions.
   0 = Disable I/O library initialization in resetprg.c. If you are not using stdio then use this value.
   1 = Enable I/O library initialization in resetprg.c. This is default and needed if you are using stdio. */
#define IO_LIB_ENABLE           (0)

#endif /* R_BSP_CONFIG_REF_HEADER_FILE */



