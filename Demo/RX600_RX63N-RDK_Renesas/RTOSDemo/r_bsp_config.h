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
* Device(s)    : RX63x
* Description  : The file r_bsp_config.h is used to configure your BSP. r_bsp_config.h should be included
*                somewhere in your package so that the r_bsp code has access to it. This file (r_bsp_config_reference.h)
*                is just a reference file that the user can use to make their own r_bsp_config.h file.
************************************************************************************************************************
* History : DD.MM.YYYY Version Description           
*         : 13.03.2012 1.00    First Release            
***********************************************************************************************************************/
#ifndef R_BSP_CONFIG_REF_HEADER_FILE
#define R_BSP_CONFIG_REF_HEADER_FILE

/***********************************************************************************************************************
Configuration Options
***********************************************************************************************************************/
/* The 'BSP_DECLARE_STACK' macro is checked so that the stack is only declared in one place (resetprg.c). Every time a 
   '#pragma stacksize' is encountered, the stack size is increased. This prevents multiplication of stack size. */
#if defined(BSP_DECLARE_STACK)
/* User Stack size in bytes. The Renesas RX toolchain sets the stack size using the #pragma stacksize directive. */
#pragma stacksize su=0x1000
/* Interrupt Stack size in bytes. The Renesas RX toolchain sets the stack size using the #pragma stacksize directive. */
#pragma stacksize si=0x400
#endif

/* Heap size in bytes. */
#define HEAP_BYTES              (0x4)

/* After reset MCU will operate in Supervisor mode. To switch to User mode, set this macro to '1'. For more information
   on the differences between these 2 modes see the CPU >> Processor Mode section of your MCU's hardware manual.
   0 = Stay in Supervisor mode.
   1 = Switch to User mode.
*/
#define RUN_IN_USER_MODE        (0)

/* To get into User Boot Mode the user must control some pins on the MCU and also set some values in ROM. These values
   in ROM are described in the Option-Setting Memory section of the hardware manual. This macro sets these values so 
   that User Boot Mode can be used. The user is still responsible for setting the MCU pins appropriately.
   0 = Single-Chip or USB Boot Mode
   1 = User Boot Mode
*/
#define USER_BOOT_ENABLE        (0)

/* Set your desired ID code. NOTE, leave at the default (all 0xFF's) if you do not wish to use an ID code. If you set 
   this value and program it into the MCU then you will need to remember the ID code because the debugger will ask for 
   it when trying to connect. Note that the E1/E20 will ignore the ID code when programming the MCU during debugging.
   If you set this value and then forget it then you can clear the ID code by connecting up in serial boot mode using 
   FDT. The ID Code is 16 bytes long. The macro below define the ID Code in 4-byte sections. */
/* Lowest 4-byte section, address 0xFFFFFFA0. From MSB to LSB: Control Code, ID code 1, ID code 2, ID code 3. */
#define ID_CODE_LONG_1          (0xFFFFFFFF)
/* 2nd ID Code section, address 0xFFFFFFA4. From MSB to LSB: ID code 4, ID code 5, ID code 6, ID code 7. */
#define ID_CODE_LONG_2          (0xFFFFFFFF)
/* 3rd ID Code section, address 0xFFFFFFA8. From MSB to LSB: ID code 8, ID code 9, ID code 10, ID code 11. */
#define ID_CODE_LONG_3          (0xFFFFFFFF)
/* 4th ID Code section, address 0xFFFFFFAC. From MSB to LSB: ID code 12, ID code 13, ID code 14, ID code 15. */
#define ID_CODE_LONG_4          (0xFFFFFFFF)

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
#define CLOCK_SOURCE            (4)

/* Clock configuration options.
   The input clock frequency is specified and then the system clocks are set by specifying the multipliers used. The
   multiplier settings are used to set the clock registers in resetprg.c. If a 12MHz clock is used and the 
   ICLK is 96MHz, PCLKA is 48MHz, PCLKB is 48MHz, FCLK is 48MHz, USB Clock is 48MHz, and BCLK is 12MHz then the 
   settings would be:

   XTAL_HZ = 12000000
   PLL_DIV = 1  (no division)
   PLL_MUL = 16 (12MHz x 16 = 192MHz)
   ICK_DIV =  2      : System Clock (ICLK)        = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / ICK_DIV)  = 96MHz
   PCKA_DIV = 4      : Peripheral Clock A (PCLKA) = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / PCKA_DIV) = 48MHz
   PCKB_DIV = 4      : Peripheral Clock B (PCLKB) = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / PCKB_DIV) = 48MHz
   FCK_DIV =  4      : Flash IF Clock (FCLK)      = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / FCK_DIV)  = 48MHz
   BCK_DIV =  8      : External Bus Clock (BCK)   = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / BCK_DIV)  = 24MHz
   UCK_DIV =  4      : USB Clock (UCLK)           = (((XTAL_HZ/PLL_DIV) * PLL_MUL) / UCK_DIV)  = 48MHz
*/
/* XTAL - Input clock frequency in Hz */
#define XTAL_HZ                 (12000000)
/* PLL Input Frequency Divider Select (PLIDIV). 
   Available divisors = /1 (no division), /2, /4
*/
#define PLL_DIV                 (1)
/* PLL Frequency Multiplication Factor Select (STC). 
   Available multipliers = x8, x10, x12, x16, x20, x24, x25, x50
*/
#define PLL_MUL                 (16)
/* System Clock Divider (ICK).
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define ICK_DIV                 (2)
/* Peripheral Module Clock A Divider (PCKA). 
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define PCKA_DIV                (2) /* WAS 4 for 48MHz, attempting to make it equal ICLK by setting it to 2. */
/* Peripheral Module Clock B Divider (PCKB). 
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define PCKB_DIV                (4)
/* External Bus Clock Divider (BCK). 
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define BCK_DIV                 (8)
/* Flash IF Clock Divider (FCK). 
   Available divisors = /1 (no division), /2, /4, /8, /16, /32, /64
*/
#define FCK_DIV                 (4)
/* IEBUS Clock Divider Select. 
   Available divisors = /1 (no division), /2, /4, /6, /8, /16, /32, /64
*/
#define IEBCK_DIV               (8)
/* USB Clock Divider Select. 
   Available divisors = /3, /4
*/
#define UCK_DIV                 (4)

#endif /* R_BSP_CONFIG_REF_HEADER_FILE */



