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
* Device(s)    : RX
* Description  : Definition of the fixed vector table
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 26.10.2011 1.00     First Release
*         : 17.02.2012 1.10     Made function names compliant with CS v4.0
*         : 13.03.2012 1.20     ID Code is now specified in r_bsp_config.h. It is still used here in Fixed_Vectors[].
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include <stdint.h>
#include <machine.h>
#include "platform.h"

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
    /* Add your own code here to handle this exception */
    nop();
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
    /* Add your own code here to handle this exception */
    nop();
}

/***********************************************************************************************************************
* Function name: excep_floating_point_isr
* Description  : Floating point exception ISR
* Arguments    : none
* Return Value : none
***********************************************************************************************************************/
#pragma interrupt (excep_floating_point_isr)
void excep_floating_point_isr(void)
{
    /* Add your own code here to handle this exception */
    nop();
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
    /* Add your own code here to handle this exception */
    nop();
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
    /* Add your own code here to handle this exception */
    nop();
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
    /* 
        To find the address that was accessed when the bus error occured, read the register BSC.BERSR2.WORD.  The upper 
        13 bits of this register contain the upper 13-bits of the offending address (in 512K byte units)
    */
    
    /* Add your own code here to handle this interrupt */
    nop();
}

/***********************************************************************************************************************
* The following array fills in the fixed vector table and the code
* protecction ID bytes.
***********************************************************************************************************************/
#pragma section C FIXEDVECT

void* const Fixed_Vectors[] = {
    
/* 0xffffff90 through 0xffffff9f: Reserved area - must be all 0xFF */
  (void *)0xFFFFFFFF,   /* 0xffffff90 - Reserved */
  (void *)0xFFFFFFFF,   /* 0xffffff94 - Reserved */
  (void *)0xFFFFFFFF,   /* 0xffffff98 - Reserved */

/* The 32-bit area immediately below (0xffffff9c through 0xffffff9f) is a special area that allows the ROM to be 
   protected from reading or writing by a parallel programmer. Please refer to the HW manual for appropriate settings.
   The default (all 0xff) places no restrictions and therefore allows reads and writes by a parallel programmer. */
  (void *)0xFFFFFFFF,   /* 0xffffff9C - ROM Code Protection */

/* The memory are immediately below (0xffffffa0 through 0xffffffaf) is a special area that allows the on-chip firmware 
   to be protected. See the section "ID Code Protection" in the HW manual for details on how to enable protection.  
   Setting the four long words below to non-0xFF values will enable protection.  Do this only after carefully review 
   the HW manual */
   
/* 0xffffffA0 through 0xffffffaf: ID Code Protection. The ID code is specified using macros in r_bsp_config.h.  */
  (void *) ID_CODE_LONG_1,  /* 0xffffffA0 - Control code and ID code */
  (void *) ID_CODE_LONG_2,  /* 0xffffffA4 - ID code (cont.) */
  (void *) ID_CODE_LONG_3,  /* 0xffffffA8 - ID code (cont.) */
  (void *) ID_CODE_LONG_4,  /* 0xffffffAC - ID code (cont.) */
  
/* 0xffffffB0 through 0xffffffcf: Reserved area */
  (void *) 0xFFFFFFFF,  /* 0xffffffB0 - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffB4 - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffB8 - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffBC - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffC0 - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffC4 - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffC8 - Reserved */
  (void *) 0xFFFFFFFF,  /* 0xffffffCC - Reserved */

/* Fixed vector table */
  (void *) excep_supervisor_inst_isr,         /* 0xffffffd0  Exception(Supervisor Instruction) */
  (void *) undefined_interrupt_source_isr,    /* 0xffffffd4  Reserved */
  (void *) undefined_interrupt_source_isr,    /* 0xffffffd8  Reserved */
  (void *) excep_undefined_inst_isr,          /* 0xffffffdc  Exception(Undefined Instruction) */
  (void *) undefined_interrupt_source_isr,    /* 0xffffffe0  Reserved */
  (void *) excep_floating_point_isr,          /* 0xffffffe4  Exception(Floating Point) */
  (void *) undefined_interrupt_source_isr,    /* 0xffffffe8  Reserved */
  (void *) undefined_interrupt_source_isr,    /* 0xffffffec  Reserved */
  (void *) undefined_interrupt_source_isr,    /* 0xfffffff0  Reserved */
  (void *) undefined_interrupt_source_isr,    /* 0xfffffff4  Reserved */
  (void *) non_maskable_isr,                  /* 0xfffffff8  NMI */
  (void *) PowerON_Reset_PC                   /* 0xfffffffc  RESET */
};
