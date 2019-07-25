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
* File Name	   : vecttbl.c
* Device(s)    : RX11x
* Description  : Definition of the fixed vector table and option setting memory.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.11.2012 0.01     Beta Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Fixed size integers. */
#include <stdint.h>
/* Used for nop(). */
#include <machine.h>
/* BSP configuration. */
#include "platform.h"

#pragma section IntPRG

/***********************************************************************************************************************
* Function name: PowerON_Reset_PC
* Description  : The reset vector points to this function.  Code execution starts in this function after reset.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
extern void PowerON_Reset_PC(void);

/***********************************************************************************************************************
* Function name: excep_supervisor_inst_isr
* Description  : Supervisor Instruction Violation ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
#pragma interrupt (excep_supervisor_inst_isr)
void excep_supervisor_inst_isr(void)
{
    /* If the user defined a callback function in r_bsp_config.h then it will be called here. */
#if defined(EXCEP_SUPERVISOR_ISR_CALLBACK)
    EXCEP_SUPERVISOR_ISR_CALLBACK();

    /* If you do not put the MCU in Supervisor mode before returning then it will just execute the same violating
       instruction again and come back in here. Since the PSW is restored from the stack when returning from the
       exception, you would need to alter the saved PSW on the stack to change to Supervisor mode. We do not do this
       here because the only 'safe' way to do this would be to write this function in assembly. Even then most users
       would probably want to handle this someway instead of just going back to the application. */
#else
    brk();
#endif
}

/***********************************************************************************************************************
* Function name: excep_undefined_inst_isr
* Description  : Undefined instruction exception ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
#pragma interrupt (excep_undefined_inst_isr)
void excep_undefined_inst_isr(void)
{
    /* If the user defined a callback function in r_bsp_config.h then it will be called here. */
#if defined(EXCEP_UNDEFINED_INSTR_ISR_CALLBACK)
    EXCEP_UNDEFINED_INSTR_ISR_CALLBACK();
#else
    brk();
#endif
}

/***********************************************************************************************************************
* Function name: non_maskable_isr
* Description  : Non-maskable interrupt ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
#pragma interrupt (non_maskable_isr)
void non_maskable_isr(void)
{
    /* If the user defined a callback function in r_bsp_config.h then it will be called here. */
#if defined(NMI_ISR_CALLBACK)
    NMI_ISR_CALLBACK();

    /* Clear NMI flag. */
    ICU.NMICLR.BIT.NMICLR = 1;
#else
    brk();
#endif
}

/***********************************************************************************************************************
* Function name: undefined_interrupt_source_isr
* Description  : All undefined interrupt vectors point to this function.
*                Set a breakpoint in this function to determine which source is creating unwanted interrupts.
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
#pragma interrupt (undefined_interrupt_source_isr)
void undefined_interrupt_source_isr(void)
{
    /* If the user defined a callback function in r_bsp_config.h then it will be called here. */
#if defined(UNDEFINED_INT_ISR_CALLBACK)
    UNDEFINED_INT_ISR_CALLBACK();
#else
    brk();
#endif
}

/***********************************************************************************************************************
* Function name: bus_error_isr
* Description  : By default, this demo code enables the Bus Error Interrupt. This interrupt will fire if the user tries
*                to access code or data from one of the reserved areas in the memory map, including the areas covered
*                by disabled chip selects. A nop() statement is included here as a convenient place to set a breakpoint
*                during debugging and development, and further handling should be added by the user for their
*                application.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
#pragma interrupt (bus_error_isr(vect=VECT(BSC,BUSERR)))
void bus_error_isr (void)
{
    /* Clear the bus error */
    BSC.BERCLR.BIT.STSCLR = 1;

    /*
        To find the address that was accessed when the bus error occurred, read the register BSC.BERSR2.WORD.  The upper
        13 bits of this register contain the upper 13-bits of the offending address (in 512K byte units)
    */

    /* If the user defined a callback function in r_bsp_config.h then it will be called here. */
#if defined(BUS_ERROR_ISR_CALLBACK)
    BUS_ERROR_ISR_CALLBACK();
#else
    nop();
#endif
}

void Dummy( void )
{
	brk();
}

/***********************************************************************************************************************
* The following array fills in the endian and option function select registers, and the fixed vector table
* bytes.
***********************************************************************************************************************/
#pragma section C FIXEDVECT

void (*const Fixed_Vectors[])(void) = {
//;0xffffffd0  Exception(Supervisor Instruction)
	excep_supervisor_inst_isr,
//;0xffffffd4  Reserved
    Dummy,
//;0xffffffd8  Reserved
    Dummy,
//;0xffffffdc  Exception(Undefined Instruction)
    undefined_interrupt_source_isr,
//;0xffffffe0  Reserved
    Dummy,
//;0xffffffe4  Reserved
    Dummy,
//;0xffffffe8  Reserved
    Dummy,
//;0xffffffec  Reserved
    Dummy,
//;0xfffffff0  Reserved
    Dummy,
//;0xfffffff4  Reserved
    Dummy,
//;0xfffffff8  NMI
    non_maskable_isr,
//;0xfffffffc  RESET
//;<<VECTOR DATA START (POWER ON RESET)>>
//;Power On Reset PC
PowerON_Reset_PC
//;<<VECTOR DATA END (POWER ON RESET)>>
};

#pragma address _MDEreg=0xffffff80 // MDE register (Single Chip Mode)
#ifdef __BIG
	const unsigned long _MDEreg = 0xfffffff8; // big
#else
	const unsigned long _MDEreg = 0xffffffff; // little
#endif




