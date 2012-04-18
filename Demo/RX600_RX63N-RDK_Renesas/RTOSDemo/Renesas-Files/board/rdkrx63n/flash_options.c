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
* File Name	   : flash_options.c
* Device(s)    : RX63x
* Description  : Some options of the RX63x are set through registers that are found in ROM. These registers and options
*                are defined in the 'Option-Setting Memory' section of the HW Manual. These memory locations are defined
*                below with descriptions of what is being set.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 31.10.2011 1.00     First Release
*         : 13.03.2012 1.10     USER_BOOT_ENABLE macro from r_bsp_config.h is now used to set Option-Setting Memory
*                               area to boot into User Boot Mode.
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Used for fixed-width typedefs. */
#include <stdint.h>
/* Determines whether user boot is used or not. */
#include "platform.h"

/* The UB Code A, UB Code B, and Endian select register B (MDEB) are located in the User Boot space. Immediately
   following the MDEB register is the User Boot Reset Vector so it is defined below as well. These settings will only
   be used when the MCU is reset in User Boot Mode. In order for the MCU to start up in User Boot Mode the following
   conditions must be met:
   1) UB code A is 55736572h and 426F6F74h.
   2) UB code B is FFFF FF07h and 0008 C04Ch.
   3) The low level is being input on the MD pin.
   4) The high level is being input on the PC7 pin. 
   Please see the Option-Setting Memory section of your MCU's HW manual for more information. */

/* 0xFF7FFFE8 - 0xFF7FFFEF : UB Code A register  
   0xFF7FFFF0 - 0xFF7FFFF7 : UB Code B register
   0xFF7FFFF8 - 0xFF7FFFFB : MDEB register
   0xFF7FFFFC - 0xFF7FFFFF : User Boot Reset Vector */

#pragma address user_boot_settings = 0xFF7FFFE8

#if USER_BOOT_ENABLE == 1
extern void PowerON_Reset_PC(void);

/* Use this array if you are using User Boot. Make sure to fill in valid address for UB Reset Vector. */
const uint32_t user_boot_settings[6] = 
{
    0x55736572,                 //Required setting for UB Code A to get into User Boot
    0x426f6f74,                 //Required setting for UB Code A to get into User Boot
    0xffffff07,                 //Required setting for UB Code B to get into User Boot
    0x0008c04c,                 //Required setting for UB Code B to get into User Boot
    /* Choose endian for user application code
       MDEB Register - Endian Select Register B
       b31:b3 Reserved (set to 1)
       b2:b0  MDE - Endian Select (0 = Big Endian, 7 = Little Endian) */                    
    0xFFFFFFFF,                 //Select Little Endian for User Boot Code 
    (uint32_t) PowerON_Reset_PC //This is the User Boot Reset Vector. When using User Boot put in the reset address here
};
#endif

/* The Endian select register S (MDES), Option function select register 1 (OFS1), and Option function select register 0
   (OFS0) are located in User ROM. */

/* 0xFFFFFF80 - 0xFFFFFF83 : MDES register
   0xFFFFFF84 - 0xFFFFFF87 : Reserved space (0xFF's)
   0xFFFFFF88 - 0xFFFFFF8B : OFS1 register
   0xFFFFFF8C - 0xFFFFFF8F : OFS0 register */

#pragma address flash_options = 0xFFFFFF80

const uint32_t flash_options[] = 
{
    /* Choose endian for user application code
       MDES Register - Endian Select Register S
       b31:b3 Reserved (set to 1)
       b2:b0  MDE - Endian Select (0 = Big Endian, 7 = Little Endian) */
    0xFFFFFFFF,     //Little Endian chosen for User Application
    0xFFFFFFFF,     //Reserved space
    /* Configure whether voltage detection 0 circuit and HOCO are enabled after reset. 
       OFS1 - Option Function Select Register 1 
       b31:b9 Reserved (set to 1)
       b8     HOCOEN - Enable/disable HOCO oscillation after a reset (0=enable, 1=disable)
       b7:b3  Reserved (set to 1)
       b2     LVDAS - Choose to enable/disable Voltage Detection 0 Circuit after a reset (0=enable, 1=disable)
       b1:b0  Reserved (set to 1) */
    0xFFFFFFFF,     //Both are disabled.
    /* Configure WDT and IWDT settings. 
       OFS0 - Option Function Select Register 0 
       b31:b29 Reserved (set to 1)
       b28     WDTRSTIRQS - WDT Reset Interrupt Request - What to do on underflow (0=take interrupt, 1=reset MCU)
       b27:b26 WDTRPSS - WDT Window Start Position Select - (0=25%, 1=50%, 2=75%, 3=100%,don't use)
       b25:b24 WDTRPES - WDT Window End Position Select - (0=75%, 1=50%, 2=25%, 3=0%,don't use)
       b23:b20 WDTCKS - WDT Clock Frequency Division Ratio - (1=/4, 4=/64, 0xF=/128, 6=/512, 7=/2048, 8=/8192)
       b19:b18 WDTTOPS - WDT Timeout Period Select - (0=1024 cycles, 1=4096, 2=8192, 3=16384)
       b17     WDTSTRT - WDT Start Mode Select - (0=auto-start after reset, halt after reset)
       b16:b15 Reserved (set to 1)
       b14     IWDTSLCSTP - IWDT Sleep Mode Count Stop Control - (0=can't stop count, 1=stop w/some low power modes)
       b13     Reserved (set to 1)
       b12     IWDTRSTIRQS - IWDT Reset Interrupt Request - What to do on underflow (0=take interrupt, 1=reset MCU)
       b11:b10 IWDTRPSS - IWDT Window Start Position Select - (0=25%, 1=50%, 2=75%, 3=100%,don't use)
       b9:b8   IWDTRPES - IWDT Window End Position Select - (0=75%, 1=50%, 2=25%, 3=0%,don't use)
       b7:b4   IWDTCKS - IWDT Clock Frequency Division Ratio - (0=none, 2=/16, 3 = /32, 4=/64, 0xF=/128, 5=/256)
       b3:b2   IWDTTOPS - IWDT Timeout Period Select - (0=1024 cycles, 1=4096, 2=8192, 3=16384)
       b1      IWDTSTRT - IWDT Start Mode Select - (0=auto-start after reset, halt after reset)
       b0      Reserved (set to 1) */
    0xFFFFFFFF
};

