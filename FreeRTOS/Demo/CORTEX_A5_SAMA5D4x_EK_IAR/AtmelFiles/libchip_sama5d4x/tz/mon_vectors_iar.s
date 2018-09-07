/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
 *
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


        	SECTION MSTACK:DATA:NOROOT(3)
                SECTION CSTACK:DATA:NOROOT(3)
#include "mon_macros.h"

#define __ASSEMBLY__


AIC         DEFINE 0xFC06E000
AIC_IVR     DEFINE 0x10
AIC_EOICR   DEFINE 0x38
SAIC        DEFINE   0xFC068400
AIC_FVR     DEFINE   0x14


        SECTION monitor_vector:CODE:NOROOT(2)
        PUBLIC monitor_vectors
        PUBLIC SM_Handler
        EXTERN NWVector
        EXTERN SwitchToNormalWorld
        EXTERN SwitchToSecureWorld
        EXTERN TZ_FIQ_Handler
        EXTERN TZ_IRQ_Handler
        EXTERN TzResetVector
        ARM

/*
 *-----------------------------------------------------------------------------
 * Monitor exception vector table
 *      Most of these exceptions does not do anything other than branching to
 *      itself except smc vector. The SMC vector jumps to smc handler which
 *      takes care of proper switching from NWd to SWd and from SWd to NWd.
 * -----------------------------------------------------------------------------
 */
monitor_vectors:
	B	.			; Reset: not used by Monitor 
	B	.			; Undef: not used by Monitor
	LDR	pc, =SM_Handler
	B	.			; Prefetch: can be used by Monitor 
	B	.			; Data abort: can be used by Monitor 
	B	.			; RESERVED */
	B	.			; IRQ: can be used by Monitor 
	B	.			; FIQ - can be used by Monitor 



        SECTION monitor:CODE:NOROOT(2)
        SECTION MSTACK:DATA:NOROOT(3)

        
        
SM_Handler:

    CPSID         IF
    PUSH   {r0-r3}                       ; r0-r3 contain args to be passed between worlds
                                         ; Temporarily stack, so can be used as scratch regs

    ; Which world have we come from
    ; ------------------------------
    MRC     p15, 0, r0, c1, c1, 0        ; Read Secure Configuration Register data
    TST     r0, #NS_BIT                  ; Is the NS bit set?
    BIC     r0, r0, #NS_BIT              ; Make sure the SCR.NS bit is now clear
//    LDRNE   r0, =SCR_SW_BIT
    MCR     p15, 0, r0, c1, c1, 0        ; Write Secure Configuration Register data
    ISB
    
    LDREQ   r2, =MON_DATA_BASE              
    LDRNE   r3, =MON_DATA_BASE 
    
    ADDEQ   r3, r2, #Struct_size
    ADDNE   r2, r3, #Struct_size

    STM	r2!, {r4-r12}                   ; Save r4 to r12 registers of current world
    LDM     r3!, {r4-r12}               ; Restore r4 to r12 registers of world we need to switch
    
    ; Save current world MON_LR MON_SP and MON_SPSR and restore for other world
    MRS     r1, SPSR
    STM     r2!, {r1, sp, lr}
    LDM     r3!, {r1, sp, lr}
    MSR     spsr_cxsf, r1
    
    ; Save current world SVC_LR, SVC_SP and SVC_SPSR and restore for other world
    CPS	    #ARM_MODE_SVC
    MRS     r1, SPSR
    STM     r2!, {r1, sp, lr}
    LDM     r3!, {r1, sp, lr}
    MSR     spsr_cxsf, r1   
    
    ; Save current world FIQ_LR FIQ_SP and FIQ_SPSR and restore for other world
    CPS	    #ARM_MODE_FIQ
    MRS     r1, SPSR
    STM     r2!, {r1, sp, lr}
    LDM     r3!, {r1, sp, lr}
    MSR     spsr_cxsf, r1   
    
    ; Save current world IRQ_LR IRQ_SP and IRQ_SPSR and restore for other world
    CPS	    #ARM_MODE_IRQ
    MRS     r1, SPSR
    STM     r2!, {r1, sp, lr}
    LDM     r3!, {r1, sp, lr}
    MSR     spsr_cxsf, r1   

    ; Change to SVC mode before going to MON mode
    CPS	    #ARM_MODE_SVC
    CPS	    #ARM_MODE_MON    
   
    CLREX                               ; Clear local monitor

    LDREQ     r0, =SCR_NW_BIT           ; set FIQ to moitor exception(optional) and NS bit to 1 if comming from secure
    MCREQ     p15, 0, r0, c1, c1, 0     ; Write Secure Configuration Register data  
    ISB
    
    /* set the monitor vector base */
    LDREQ     r2, =NWVector
    MCREQ     p15, 0, r2, c12, c0, 0	 ; non secure copy of VBAR
    
    BNE       secureworld  
  
nonsecureworld:  
    CPSIE     IF

secureworld:  
    CPSIE     F
  
    ; Now restore args (r0-r3)
    ; -------------------------
    POP     {r0-r3}

    
    ; exception return
    ; -------------------------
    MOVS    pc, lr
  
  
  
//***************************************************//
; Monitor initialization code
//***************************************************//

        SECTION monitor:CODE:NOROOT(2)
        SECTION MSTACK:DATA:NOROOT(3)
        
        PUBLIC SecureMonitor_init
        EXTERN nw_start
        EXTERN TzResetVector
        
        ARM

SecureMonitor_init:
        
       
	/* Switch to MON mode */
	MRS	r4, cpsr
	CPS     #ARM_MODE_MON           ; change back to SVC mode

        /* set the monitor stack */
	LDR	sp, =SFE(MSTACK)
        BIC     sp,sp,#0x7                      ; Make sure SP is 8 aligned
        
        /* set the monitor vector base */
	LDR	r2, =monitor_vectors            ; Update monitor exception vector table addr
	MCR	p15, 0, r2, c12, c0, 1        

        MSR     cpsr_c, r4                  ; change back to SVC mode
        
         /* set the monitor vector base */
	LDR	r2, =TzResetVector              ; Update secure exception vector table addr
	MCR	p15, 0, r2, c12, c0, 0
        
        // Load zero to context memory block
        MOV     r3, #0
        LDR     r0, =MON_DATA_SIZE
        LDR     r1, =MON_DATA_BASE
        MOV     r2, #0  
        
loop_init:        
        CMP     r2, r0
        STRNE   r3,[r1]
        ADD     r1, r1, #4
        ADD     r2, r2, #1
        BNE     loop_init
        
        BX      lr       


  END