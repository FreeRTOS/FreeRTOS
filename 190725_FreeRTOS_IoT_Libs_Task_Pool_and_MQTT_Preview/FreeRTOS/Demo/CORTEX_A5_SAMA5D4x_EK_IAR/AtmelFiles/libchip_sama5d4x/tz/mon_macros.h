/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 *------------------------------------------------------------------------------
 * MON_DATA_BASE area is used by the monitor to save and restore
 * all resources affected by the context switching.
 * - All general purpose ARM registers
 * - Any coprocessor registers, such as NEON or VFP
 *   (not needed in our case as we are not dealing with floating point in SWd)
 * - Any world-dependant processor configuration state in CP15
 *   (TODO: what does it cover?)
 *
 * Note: we consider that there is no IRQ nor FIQ management in SWd.
 *
 * r0-r7, r12 registers are considered as corruptbile
 * r8-r11 and lr, sp and cpsr needs to be properly saved and restored
 * NWd call to SWd function:
 *      Save    -> r8-r11, svc_lr and svc_sp, cpsr
 *      Restore -> svc_sp, and cpsr
 * SWd return after completing service function execution:
 *      Save    -> svc_lr, svc_sp, and cpsr
 *      Restore -> r8-r11, svc_lr and svc_sp, cpsr
 *------------------------------------------------------------------------------
 */



#ifndef __MON_MACROS_H__
#define __MON_MACROS_H__


/*
 * Secure Configuration Register
 */

#define NS_BIT		        0x01
#define SCR_NW_BIT		0x25
#define SCR_SW_BIT		0x22

/*
 *----------------------------------------------------------------------------
 * Standard definitions of ARM processor mode bits
 *----------------------------------------------------------------------------
 */
#define MODE_MSK         0x1F            // Bit mask for mode bits in CPSR
#define ARM_MODE_ABT     0x17
#define ARM_MODE_FIQ     0x11
#define ARM_MODE_IRQ     0x12
#define ARM_MODE_SVC     0x13
#define ARM_MODE_MON     0x16
#define ARM_MODE_SYS     0x1F
#define ARM_MODE_UND     0x1B
#define I_BIT            0x80
#define F_BIT            0x40

#define CHANGE_TO_SVC_MODE    asm volatile ("CPS   #0x13");
#define CHANGE_TO_MON_MODE    asm volatile ("CPS   #0x16");


#define INITIAL_NWD_STATE	0x1D3
   


#define Struct_size            0x54
   
/* Stacks configuration */
#define STACK_SIZE		0x1FF
#define MON_DATA_BASE_SIZE	0x100

/* Stacks are descending */
#if defined (ddram)   
    #define MON_DATA_BASE       0x23FFFE00
    #define MON_DATA_END        0x24000000
#elif defined (sram)   
   #define MON_DATA_BASE        0x21FE00
   #define MON_DATA_END         0x220000   
#else
    #define MON_DATA_BASE       0x23FFFE00
    #define MON_DATA_END        0x24000000
#endif


#define MON_DATA_SIZE           ((MON_DATA_END - MON_DATA_BASE) >> 2)

#endif /* #ifndef __MON_MACROS_H__ */

